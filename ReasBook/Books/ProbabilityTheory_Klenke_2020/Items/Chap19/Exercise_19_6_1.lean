/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Corollary_17_48
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Example_19_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Corollary_19_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_14
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {Ξ : Type v} [MeasurableSpace Ξ]

variable {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- Helper for Exercise 19.6.1: the shifted future path of a discrete-time process after time
`k`. -/
private def natFuturePath (X : ℕ → Ω → E) (k : ℕ) : Ω → ℕ → E :=
  fun ω n ↦ X (n + k) ω

/-- Helper for Exercise 19.6.1: the shifted future-path map is measurable once each process
coordinate is measurable. -/
private theorem measurable_natFuturePath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (natFuturePath X k) := by
  -- Proof comment: each shifted coordinate is the measurable slice `X (n + k)`.
  refine measurable_pi_lambda _ fun n ↦ ?_
  simpa [natFuturePath, Nat.add_comm] using hX_meas (n + k)

/-- Helper for Exercise 19.6.1: the finite prefix of a discrete-time process up to time `k`. -/
private def pastPath (X : ℕ → Ω → E) (k : ℕ) : Ω → Fin (k + 1) → E :=
  fun ω i ↦ X i ω

/-- Helper for Exercise 19.6.1: the standard shifted path notation for a discrete-time process. -/
private def shiftedPath (X : ℕ → Ω → E) (k : ℕ) : Ω → ℕ → E :=
  natFuturePath X k

/-- Helper for Exercise 19.6.1: the ordered finite future coordinates after time `k`. -/
private def shiftedPathCoordinates {n : ℕ}
    (X : ℕ → Ω → E) (k : ℕ) (t : Fin n → ℕ) :
    Ω → Fin n → E :=
  fun ω i ↦ X (t i + k) ω

/-- Helper for Exercise 19.6.1: the finite-history map `pastPath X k` is measurable once each
coordinate of `X` is measurable. -/
private theorem measurable_pastPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (pastPath X k) := by
  -- Proof comment: measurability on the finite product is coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [pastPath] using hX_meas i

/-- Helper for Exercise 19.6.1: the shifted path map is measurable once each process coordinate
is measurable. -/
private theorem measurable_shiftedPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) :
    Measurable (shiftedPath X k) := by
  -- Proof comment: this is exactly the measurable shifted-path map already named above.
  simpa [shiftedPath] using measurable_natFuturePath X hX_meas k

/-- Helper for Exercise 19.6.1: finite ordered coordinates of the shifted path are measurable. -/
private theorem measurable_shiftedPathCoordinates {n : ℕ}
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (k : ℕ) (t : Fin n → ℕ) :
    Measurable (shiftedPathCoordinates X k t) := by
  -- Proof comment: each tuple coordinate is the measurable slice `X (t i + k)`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [shiftedPathCoordinates, Nat.add_comm] using hX_meas (t i + k)

/-- Helper for Exercise 19.6.1: the time-`k` generated filtration is the pullback sigma-algebra of
the finite-history map `pastPath X k`. -/
private theorem generatedFiltrationSpace_eq_pastPath_comap
    (X : ℕ → Ω → E) (k : ℕ) :
    generatedFiltrationSpace X k = MeasurableSpace.comap (pastPath X k) inferInstance := by
  have hleft :
      MeasurableSpace.comap (pastPath X k) inferInstance ≤ generatedFiltrationSpace X k := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace X k] (fun ω ↦ fun i : Fin (k + 1) ↦ X i ω) := by
      -- Proof comment: every coordinate of the finite history is already measurable at time `k`.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact
        le_iSup_of_le i <|
          le_iSup_of_le (show (i : ℕ) ≤ k from Nat.le_of_lt_succ i.2) le_rfl
    exact hPastMeas.comap_le
  have hright :
      generatedFiltrationSpace X k ≤ MeasurableSpace.comap (pastPath X k) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (k + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (pastPath X k))
    simpa [pastPath, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Exercise 19.6.1: every Nat-indexed path measure is the projective limit of its
finite restriction marginals. -/
private theorem natPathMeasure_isProjectiveLimit_restrictions
    (ν : Measure (ℕ → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset ℕ ↦ ν.map J.restrict) := by
  -- Proof comment: the projective-limit compatibility is exactly the defining restriction
  -- pushforward.
  intro J
  rfl

/-- Helper for Exercise 19.6.1: reindexing the sorted tuple attached to `J.orderEmbOfFin`
recovers the ordinary finite restriction map. -/
private theorem piCongrLeft_orderEmbOfFin_eq_restrict
    (J : Finset ℕ) (y : ℕ → E) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) = J.restrict y := by
  -- Proof comment: the order isomorphism turns the sorted tuple back into the usual restriction.
  dsimp
  ext j
  have hindex :
      J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
        (fun i ↦ y (J.orderEmbOfFin rfl i)) j) =
      J.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [hindex]

/-- Helper for Exercise 19.6.1: reindexing the ordered shifted coordinates by `J.orderEmbOfFin`
matches the usual finite restriction event. -/
private theorem shiftedPathIndicator_eq_restrictIndicator
    (X : ℕ → Ω → E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    let A' : Set (Fin J.card → E) :=
      (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
    (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
        (shiftedPathCoordinates X k t ω)) =
      fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
        (J.restrict (shiftedPath X k ω)) := by
  dsimp
  funext ω
  have hEq :
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedPathCoordinates X k (J.orderEmbOfFin rfl) ω) =
        J.restrict (shiftedPath X k ω) := by
    calc
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedPathCoordinates X k (J.orderEmbOfFin rfl) ω)
          =
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
              (fun i ↦ shiftedPath X k ω (J.orderEmbOfFin rfl i)) := by
                rfl
      _ = J.restrict (shiftedPath X k ω) := by
            simpa using
              piCongrLeft_orderEmbOfFin_eq_restrict (J := J) (y := shiftedPath X k ω)
  have hmem :
      shiftedPathCoordinates X k (J.orderEmbOfFin rfl) ω ∈
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A)
        ↔ J.restrict (shiftedPath X k ω) ∈ A := by
    simpa using show
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedPathCoordinates X k (J.orderEmbOfFin rfl) ω) ∈ A ↔
        J.restrict (shiftedPath X k ω) ∈ A from by rw [hEq]
  by_cases hω : J.restrict (shiftedPath X k ω) ∈ A
  · have hω' :
        shiftedPathCoordinates X k (J.orderEmbOfFin rfl) ω ∈
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) :=
      hmem.mpr hω
    simp [hω, hω']
  · have hω' :
        shiftedPathCoordinates X k (J.orderEmbOfFin rfl) ω ∉
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := by
        intro hω'
        exact hω (hmem.mp hω')
    simp [hω, hω']

/-- Helper for Exercise 19.6.1: evaluating a composed kernel on a restricted pushforward equals
the corresponding set integral of row masses. -/
private theorem kernelCompRestrictMapRealEqSetIntegral
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → E} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure E := (μ.restrict B).map Y
  have hkernel_int :
      Integrable (fun y : E ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable
        (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : E ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    change
      ∫ y, (κ y).real A ∂((μ.restrict B).map Y) =
        ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hmap_real

/-- Helper for Exercise 19.6.1: evaluating a Nat-indexed path measure on a finite restriction
preimage is the same as evaluating its pushforward along that restriction. -/
private theorem kernelReal_restrictPreimage_eq_mapRestrictReal
    (ν : Measure (ℕ → E)) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ν.real (J.restrict ⁻¹' A) = ((ν.map J.restrict).real A) := by
  -- Proof comment: this is the standard `map_measureReal_apply` rewrite for the measurable
  -- restriction map `J.restrict`.
  simpa using
    (MeasureTheory.map_measureReal_apply (μ := ν) (f := J.restrict)
      (Finset.measurable_restrict J) hA).symm

/-- Helper for Exercise 19.6.1: integrating the ordered-tuple indicator of a finite restriction
event against a Nat-indexed path measure recovers the corresponding restricted pushforward mass. -/
private theorem orderedTupleIndicatorIntegral_eq_mapRestrictReal
    (ν : Measure (ℕ → E)) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    let A' : Set (Fin J.card → E) :=
      (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
    (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂ν) =
      ((ν.map J.restrict).real A) := by
  dsimp
  -- Proof comment: rewrite the ordered tuple event as the ordinary restriction preimage and then
  -- use the standard `integral_indicator_one` / `map_measureReal_apply` identities.
  calc
    ∫ y, Set.indicator ((fun z ↦
          (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A)
          (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (fun i ↦ y (J.orderEmbOfFin rfl i)) ∂ν
        =
          ∫ y, Set.indicator (J.restrict ⁻¹' A) (fun _ : ℕ → E ↦ (1 : ℝ)) y ∂ν := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
            have hEq := piCongrLeft_orderEmbOfFin_eq_restrict (J := J) (y := y)
            have hmem :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈
                    ((fun z ↦
                      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                        ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) ↔
                  y ∈ J.restrict ⁻¹' A := by
              simpa using show
                (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
                    (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈ A ↔
                  J.restrict y ∈ A from by rw [hEq]
            by_cases hy : y ∈ J.restrict ⁻¹' A
            · have hy' :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈
                  ((fun z ↦
                    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                      ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := hmem.mpr hy
              simp [hy, hy']
            · have hy' :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∉
                  ((fun z ↦
                    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                      ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := by
                  intro hy'
                  exact hy (hmem.mp hy')
              simp [hy, hy']
    _ = ν.real (J.restrict ⁻¹' A) := by
          simpa using
            (MeasureTheory.integral_indicator_one (μ := ν)
              (s := J.restrict ⁻¹' A)
              ((Finset.measurable_restrict J) hA))
    _ = ((ν.map J.restrict).real A) := by
          simpa using kernelReal_restrictPreimage_eq_mapRestrictReal (ν := ν) (J := J) hA

/-- Helper for Exercise 19.6.1: transport the Chapter 17 ordered-coordinate conditional-
expectation formula from the natural-number submonoid of `NNReal` back to the discrete-time `ℕ`
indexing used in this file. -/
private theorem orderedFutureCoordinateCondExp_of_markovProcessNat
    {m : ℕ} (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (f : (Fin m → E) → ℝ)
    (hf_meas : Measurable f) (hf_bdd : Bornology.IsBounded (Set.range f))
    (t : Fin m → ℕ) (ht : Monotone t) :
    ((P x : Measure Ω)[fun ω ↦ f (shiftedPathCoordinates X k t ω) |
        generatedFiltrationSpace X k]) =ᵐ[(P x : Measure Ω)]
      fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) := by
  let Iℕ : AddSubmonoid NNReal := {
    carrier := {r | ∃ n : ℕ, ((n : ℕ) : NNReal) = r}
    zero_mem' := by
      exact ⟨0, by simp⟩
    add_mem' := by
      intro a b ha hb
      rcases ha with ⟨m, hm⟩
      rcases hb with ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      simpa [hm, hn] }
  let natTime : ℕ → Iℕ := fun n ↦
    ⟨n, by
      exact ⟨n, rfl⟩⟩
  let natIndex : Iℕ → ℕ := fun s ↦
    Classical.choose (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  let Xnat : Iℕ → Ω → E := fun s ω ↦ X (natIndex s) ω
  let reindexPath : (ℕ → E) → Iℕ → E := fun y s ↦ y (natIndex s)
  let κnat : Kernel E (Iℕ → E) := κ.map reindexPath
  let tnat : Fin m → Iℕ := fun i ↦ natTime (t i)
  have hnatIndex_spec : ∀ s : Iℕ, ((natIndex s : ℕ) : NNReal) = s.1 := by
    intro s
    exact Classical.choose_spec (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  have hnatIndex_natTime : ∀ n : ℕ, natIndex (natTime n) = n := by
    intro n
    have hcast : (((natIndex (natTime n) : ℕ) : ℕ) : NNReal) = n := by
      simpa [natTime] using hnatIndex_spec (natTime n)
    exact_mod_cast hcast
  have hnatTime_natIndex : ∀ s : Iℕ, natTime (natIndex s) = s := by
    intro s
    apply Subtype.ext
    exact hnatIndex_spec s
  have hnatIndex_add : ∀ s u : Iℕ, natIndex (s + u) = natIndex s + natIndex u := by
    intro s u
    have hcast :
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) =
          ((natIndex s + natIndex u : ℕ) : NNReal) := by
      calc
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) = (s + u).1 := hnatIndex_spec (s + u)
        _ = s.1 + u.1 := rfl
        _ = (((natIndex s : ℕ) : ℕ) : NNReal) + (((natIndex u : ℕ) : ℕ) : NNReal) := by
              rw [hnatIndex_spec s, hnatIndex_spec u]
        _ = ((natIndex s + natIndex u : ℕ) : NNReal) := by simp
    exact_mod_cast hcast
  have hnatTime_le_iff : ∀ {n l : ℕ}, natTime n ≤ natTime l ↔ n ≤ l := by
    intro n l
    change ((n : NNReal) ≤ (l : NNReal)) ↔ n ≤ l
    norm_num
  have hsub : ∀ ⦃s u : Iℕ⦄, s ≤ u → u.1 - s.1 ∈ Iℕ := by
    intro s u hsu
    change ∃ n : ℕ, ((n : ℕ) : NNReal) = u.1 - s.1
    refine ⟨natIndex u - natIndex s, ?_⟩
    have hle : natIndex s ≤ natIndex u := by
      have : natTime (natIndex s) ≤ natTime (natIndex u) := by
        simpa [hnatTime_natIndex] using hsu
      exact hnatTime_le_iff.mp this
    calc
      (((natIndex u - natIndex s : ℕ) : ℕ) : NNReal)
          = ((natIndex u : ℕ) : NNReal) - ((natIndex s : ℕ) : NNReal) := by
              simpa [Nat.cast_sub hle]
      _ = u.1 - s.1 := by rw [hnatIndex_spec u, hnatIndex_spec s]
  have hreindex_meas : Measurable reindexPath := by
    -- Proof comment: the transported path reindexing is coordinatewise evaluation at the chosen
    -- natural representative of each submonoid time.
    refine measurable_pi_lambda _ fun s ↦ ?_
    exact measurable_pi_apply (natIndex s)
  have hpathMap_meas : Measurable (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := by
    -- Proof comment: the original trajectory map is measurable because each coordinate of `X` is.
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  have hgenerated :
      ∀ n : ℕ, generatedFiltrationSpace Xnat (natTime n) = generatedFiltrationSpace X n := by
    intro n
    rw [generatedFiltrationSpace, generatedFiltrationSpace]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun s hs ↦ ?_
      have hs' : natIndex s ≤ n := by
        have : natTime (natIndex s) ≤ natTime n := by
          simpa [hnatTime_natIndex] using hs
        exact hnatTime_le_iff.mp this
      have hcomap :
          MeasurableSpace.comap (X (natIndex s)) inferInstance ≤ generatedFiltrationSpace X n := by
        exact le_iSup_of_le (natIndex s) <| le_iSup_of_le hs' le_rfl
      simpa [Xnat] using hcomap
    · refine iSup₂_le fun r hr ↦ ?_
      have hr' : natTime r ≤ natTime n := hnatTime_le_iff.mpr hr
      have hcomap :
          MeasurableSpace.comap (Xnat (natTime r)) inferInstance ≤
            generatedFiltrationSpace Xnat (natTime n) := by
        exact le_iSup_of_le (natTime r) <| le_iSup_of_le hr' le_rfl
      simpa [Xnat, hnatIndex_natTime] using hcomap
  have hgenerated' :
      ∀ s : Iℕ, generatedFiltrationSpace Xnat s = generatedFiltrationSpace X (natIndex s) := by
    intro s
    calc
      generatedFiltrationSpace Xnat s
          = generatedFiltrationSpace Xnat (natTime (natIndex s)) := by
              rw [hnatTime_natIndex s]
      _ = generatedFiltrationSpace X (natIndex s) := hgenerated (natIndex s)
  have htransition : ∀ s : Iℕ, transitionKernel κnat s = transitionKernel κ (natIndex s) := by
    intro s
    ext y A hA
    rw [transitionKernel_apply, transitionKernel_apply]
    have hrow : κnat y = (κ y).map reindexPath := by
      simpa [κnat] using Kernel.map_apply κ hreindex_meas y
    rw [hrow]
    rw [Measure.map_map (μ := κ y) (f := reindexPath) (g := fun z : Iℕ → E ↦ z s)
      (measurable_pi_apply s) hreindex_meas]
    rfl
  letI : IsTimeHomogeneousMarkovProcess Xnat P κnat := by
    refine
      { measurable_process := fun s ↦ by simpa [Xnat] using hX_meas (natIndex s)
        initial_state := ?_
        path_law := ?_
        markov_property := ?_ }
    · intro y
      have hzero : natIndex (0 : Iℕ) = 0 := by
        have : (0 : Iℕ) = natTime 0 := by
          apply Subtype.ext
          simp [natTime]
        simpa [this] using hnatIndex_natTime 0
      simpa [Xnat, hzero] using hX0 y
    · intro y
      calc
        κnat y = ((κ y).map reindexPath) := by
              simpa [κnat] using Kernel.map_apply κ hreindex_meas y
        _ = (((P y : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)).map reindexPath) := by
              rw [hpath y]
        _ = (P y : Measure Ω).map (fun ω : Ω ↦ fun s : Iℕ ↦ Xnat s ω) := by
              rw [Measure.map_map hreindex_meas hpathMap_meas]
              rfl
    · intro y A hA s u
      have hsum : Xnat (u + s) ⁻¹' A = X (natIndex u + natIndex s) ⁻¹' A := by
        ext ω
        simp [Xnat, hnatIndex_add]
      have hright :
          (fun ω ↦ ((transitionKernel κnat u) (Xnat s ω)).real A) =
            fun ω ↦ ((transitionKernel κ (natIndex u)) (X (natIndex s) ω)).real A := by
        funext ω
        rw [htransition u]
      -- Proof comment: after identifying the transported time indices and history sigma-algebras,
      -- the Markov property is exactly the original `ℕ`-indexed owner field.
      simpa [hsum, hgenerated' s, hright] using
        (hMarkov.markov_property y hA (natIndex s) (natIndex u))
  have hordered :
      HasOrderedFutureCoordinateConditionalExpectationFormula Xnat P κnat :=
    hasOrderedFutureCoordinateConditionalExpectationFormula_of_isTimeHomogeneousMarkovProcess
      Xnat P κnat hsub
  have htnat : Monotone tnat := by
    intro i j hij
    exact hnatTime_le_iff.mpr (ht hij)
  have horderedNat :
      (P x : Measure Ω)[fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω) |
          generatedFiltrationSpace Xnat (natTime k)] =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω) := by
    -- Proof comment: this is the Chapter 17 ordered-coordinate formula on the transported
    -- natural-number submonoid.
    have hk_nonneg : 0 ≤ natTime k := by
      show (0 : NNReal) ≤ ((natTime k : Iℕ) : NNReal)
      exact zero_le _
    simpa using hordered hf_meas hf_bdd (t := tnat) htnat (natTime k) x hk_nonneg
  have hleft :
      (fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω)) =
        fun ω ↦ f (shiftedPathCoordinates X k t ω) := by
    -- Proof comment: after transport, the Chapter 17 future coordinates become the local
    -- shifted-coordinate tuple `ω ↦ (X (k + t i) ω)_i`.
    funext ω
    congr 1
    funext i
    simp [futurePathCoordinates, shiftedPathCoordinates, Xnat, tnat, natTime, hnatIndex_add,
      hnatIndex_natTime, add_comm]
  have hright :
      (fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω)) =
        fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) := by
    -- Proof comment: the transported path-kernel row is just the original row seen through the
    -- index reparameterization `natIndex`.
    funext ω
    have htuple_meas :
        Measurable (fun y : Iℕ → E ↦ f (fun i ↦ y (tnat i))) := by
      refine hf_meas.comp ?_
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply (tnat i)
    have hrow : κnat (Xnat (natTime k) ω) = (κ (X k ω)).map reindexPath := by
      rw [show Xnat (natTime k) ω = X k ω by simp [Xnat, hnatIndex_natTime]]
      simpa [κnat] using Kernel.map_apply κ hreindex_meas (X k ω)
    rw [hrow]
    rw [MeasureTheory.integral_map hreindex_meas.aemeasurable htuple_meas.aestronglyMeasurable]
    congr 1 with y
    congr 1
    funext i
    simp [reindexPath, tnat, hnatIndex_natTime]
  calc
    (P x : Measure Ω)[fun ω ↦ f (shiftedPathCoordinates X k t ω) | generatedFiltrationSpace X k]
        =ᵐ[(P x : Measure Ω)]
          (P x : Measure Ω)[fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω) |
            generatedFiltrationSpace Xnat (natTime k)] := by
              rw [hgenerated k]
              exact MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hleft.symm)
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω) :=
      horderedNat
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) :=
      Filter.EventuallyEq.of_eq hright

/-- Helper for Exercise 19.6.1: Theorem 17.9 gives the conditional law of every finite shifted
future restriction on a history event. -/
private theorem futurePathRestrictionIndicator_condExp
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ((P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ))
        (J.restrict (shiftedPath X k ω)) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
  let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
  let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
  let A' : Set (Fin J.card → E) :=
    (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
  have hA'_meas : MeasurableSet A' := by
    exact hA.preimage ((MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e).measurable)
  have hIndicator_meas :
      Measurable (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ)) := by
    -- Proof comment: the finite-coordinate event indicator is measurable on the ordered tuple
    -- space.
    exact Measurable.indicator measurable_const hA'_meas
  have hIndicator_bdd :
      Bornology.IsBounded (Set.range (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))) := by
    -- Proof comment: the indicator takes only the values `0` and `1`.
    simpa [A'] using isBounded_range_indicator_one A'
  have hFiniteIndicator :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedPathCoordinates X k t ω) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    -- Proof comment: transport the Chapter 17 ordered-coordinate formula through the natural
    -- numbers seen as an additive submonoid of `NNReal`.
    exact
      orderedFutureCoordinateCondExp_of_markovProcessNat
        (X := X) (P := P) (κ := κ) (hX_meas := hX_meas) (hX0 := hX0) (hpath := hpath)
        x k (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))
        hIndicator_meas hIndicator_bdd t
        (by simpa [t] using (J.orderEmbOfFin rfl).monotone)
  have hleft_fun :
      (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedPathCoordinates X k t ω)) =
        fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedPath X k ω)) := by
    -- Proof comment: the ordered tuple event is exactly the same finite restriction event after
    -- reindexing by the order isomorphism of `J`.
    simpa [e, t, A'] using
      shiftedPathIndicator_eq_restrictIndicator (X := X) (k := k) (J := J) (A := A)
  have hFiniteIndicator' :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedPath X k ω)) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    simpa [hleft_fun] using hFiniteIndicator
  filter_upwards [hFiniteIndicator'] with ω hω
  have hright :
      (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂κ (X k ω)) =
        (((κ (X k ω)).map J.restrict).real A) := by
    -- Proof comment: the auxiliary integral is exactly the restricted path-kernel mass by the
    -- finite-restriction integral helper.
    simpa [e, t, A'] using
      orderedTupleIndicatorIntegral_eq_mapRestrictReal (ν := κ (X k ω)) (J := J) hA
  simpa [hright] using hω

/-- Helper for Exercise 19.6.1: on each history event, the restricted shifted-future law agrees
with the path kernel mixed against the present-state law. -/
private theorem restrictedFuturePathLaw_eq_mixedPathLaw_on_history
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (n : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X n] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedPath X n)
    let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X n))
    νB = ρB := by
  let μ : Measure Ω := (P x : Measure Ω)
  let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedPath X n)
  let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X n))
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X n]
    exact (measurable_pastPath X hX_meas n).comap_le
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  have hJ :
      ∀ J : Finset ℕ, νB.map J.restrict = ρB.map J.restrict := by
    intro J
    let κJ : Kernel E (J → E) := κ.map J.restrict
    letI : IsMarkovKernel κJ := by
      let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
        Finset.measurable_restrict J
      refine ⟨fun y : E ↦ ?_⟩
      have hrow : κJ y = (κ y).map J.restrict := by
        simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
      rw [hrow]
      simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
    refine Measure.ext fun A hA ↦ ?_
    let futureEvent : Set Ω := (fun ω ↦ J.restrict (shiftedPath X n ω)) ⁻¹' A
    have hfuture_meas : MeasurableSet futureEvent := by
      simpa [futureEvent] using
        ((Finset.measurable_restrict J).comp (measurable_shiftedPath X hX_meas n)) hA
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace X n⟧ =ᵐ[μ]
          fun ω ↦ (((κ (X n ω)).map J.restrict).real A) := by
      -- Proof comment: the finite-restriction conditional-law formula gives the event mass on
      -- each history event.
      simpa [futureEvent] using
        futurePathRestrictionIndicator_condExp X P κ hX_meas hX0 hpath x n J hA
    have hleft_real :
        (((νB.map J.restrict).real A)) = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
      have hmass :
          μ.real (B ∩ futureEvent) =
            ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
        calc
          μ.real (B ∩ futureEvent)
              = ∫ ω in B, (μ⟦futureEvent | generatedFiltrationSpace X n⟧) ω ∂μ := by
                  rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hB,
                    ← MeasureTheory.integral_indicator hB_ambient]
                  simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                    (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                      (hB_ambient.inter hfuture_meas)).symm
          _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
                exact MeasureTheory.integral_congr_ae hmarkov.restrict
      have hmapJ :
          νB.map J.restrict = (μ.restrict B).map (fun ω ↦ J.restrict (shiftedPath X n ω)) := by
        dsimp [νB]
        rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict J).aemeasurable]
        · rfl
        · exact (measurable_shiftedPath X hX_meas n).aemeasurable
      calc
        (((νB.map J.restrict).real A))
            = ((((μ.restrict B).map (fun ω ↦ J.restrict (shiftedPath X n ω))).real A)) := by
                rw [hmapJ]
        _ = (μ.restrict B).real futureEvent := by
              simpa [futureEvent] using
                (MeasureTheory.map_measureReal_apply
                  (μ := (μ.restrict B)) (f := fun ω ↦ J.restrict (shiftedPath X n ω))
                  ((Finset.measurable_restrict J).comp (measurable_shiftedPath X hX_meas n)) hA)
        _ = μ.real (futureEvent ∩ B) := by
              simpa [futureEvent] using
                (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B) (t := futureEvent)
                  hfuture_meas)
        _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
              simpa [Set.inter_comm] using hmass
    have hright_real :
        (((ρB.map J.restrict).real A)) = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
      let κJ : Kernel E (J → E) := κ.map J.restrict
      have hmap :
          ρB.map J.restrict = κJ ∘ₘ ((μ.restrict B).map (X n)) := by
        dsimp [ρB, κJ]
        simpa using Measure.map_comp (((μ.restrict B).map (X n))) κ (Finset.measurable_restrict J)
      haveI : IsMarkovKernel κJ := by
        let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
          Finset.measurable_restrict J
        refine ⟨fun y : E ↦ ?_⟩
        have hrow : κJ y = (κ y).map J.restrict := by
          simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
        rw [hrow]
        simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
      rw [hmap]
      calc
        ((κJ ∘ₘ ((μ.restrict B).map (X n))).real A)
            = ∫ ω in B, (κJ (X n ω)).real A ∂μ := by
                simpa [κJ] using
                  (kernelCompRestrictMapRealEqSetIntegral
                    (κ := κ.map J.restrict) (μ := μ) (Y := X n) (hY := hX_meas n)
                    (B := B) hB_ambient (A := A) hA)
        _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hrow : κJ (X n ω) = (κ (X n ω)).map J.restrict := by
                simpa [κJ] using Kernel.map_apply κ (Finset.measurable_restrict J) (X n ω)
              exact congrArg (fun ν : Measure (J → E) ↦ ν.real A) hrow
    have hleft_ne_top : (νB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (νB.map J.restrict) A
    have hright_ne_top : (ρB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (ρB.map J.restrict) A
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map J.restrict) (ν := ρB.map J.restrict)
        (s := A) (t := A) hleft_ne_top hright_ne_top).mp
        (hleft_real.trans hright_real.symm)
  have hν :
      MeasureTheory.IsProjectiveLimit νB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    simpa [νB] using natPathMeasure_isProjectiveLimit_restrictions νB
  have hρ :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ ρB.map J.restrict) := by
    simpa [ρB] using natPathMeasure_isProjectiveLimit_restrictions ρB
  have hρ' :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    intro J
    exact (hJ J).symm
  haveI : ∀ J : Finset ℕ, IsFiniteMeasure (νB.map J.restrict) := fun _ ↦ inferInstance
  -- Proof comment: equality of all finite restrictions identifies the full path measures by
  -- projective-limit uniqueness.
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ'

/-- Helper for Exercise 19.6.1: the discrete-time Markov owner gives the full deterministic-time
conditional-expectation formula for bounded shifted future-path functionals. -/
private theorem futurePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (shiftedPath X k ω) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  let μ : Measure Ω := (P x : Measure Ω)
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    exact (measurable_pastPath X hX_meas k).comap_le
  have hfuture_meas : Measurable (shiftedPath X k) := measurable_shiftedPath X hX_meas k
  have hg_int :
      Integrable (fun ω ↦ g (shiftedPath X k ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    -- Proof comment: bounded measurable path observables are integrable under the start law.
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨shiftedPath X k ω, rfl⟩
  have hXk_generated : Measurable[generatedFiltrationSpace X k] (X k) := by
    -- Proof comment: the present state is the last coordinate of the finite history map.
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω (Fin.last k)) := by
      exact (measurable_pi_apply (Fin.last k)).comp (comap_measurable (pastPath X k))
    simpa [pastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    -- Proof comment: integrating a measurable real-valued path functional against the kernel is
    -- measurable in the starting state.
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X k] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    -- Proof comment: compose the measurable kernel integral with the history-measurable present
    -- state.
    exact hKernelIntegral_meas.comp hXk_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp (hX_meas k)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :=
    MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        -- Proof comment: the kernel-integral candidate is bounded on every finite history event.
        refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hbound_row :
            ‖∫ y, g y ∂κ (X k ω)‖ ≤ C := by
          have hgC : ∀ᵐ y ∂κ (X k ω), ‖g y‖ ≤ C := by
            exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X k ω)) hgC)
        exact hbound_row)
      (fun s hs hμs ↦ by
        -- Proof comment: on each history event, identify the restricted future-path law with the
        -- mixed path-kernel law and then integrate `g` against that common path measure.
        let νB : Measure (ℕ → E) := (μ.restrict s).map (shiftedPath X k)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X k))
        have hs_history : MeasurableSet[generatedFiltrationSpace X k] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedFuturePathLaw_eq_mixedPathLaw_on_history X P κ hX_meas hX0 hpath x k
              hs_history
        haveI : IsFiniteMeasure νB := by
          dsimp [νB]
          infer_instance
        have hg_νB_int : Integrable g νB := by
          refine Integrable.of_bound hg_meas.aestronglyMeasurable C ?_
          exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
        have hg_ρB_int : Integrable g ρB := by
          rw [← hlaw]
          exact hg_νB_int
        have hleft :
            ∫ ω in s, g (shiftedPath X k ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (shiftedPath X k ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (shiftedPath X k) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hg_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, g y ∂ρB = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict s).map (X k))
          have hcomp :
              (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, g y ∂ρB = ∫ y, g y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, g y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ₀) (a := ())
                      hg_ρB_int)
            _ = ∫ z, ∫ y, g y ∂κ z ∂((μ.restrict s).map (X k)) := by
                  simp [κ₀]
            _ = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas k).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable
  exact hCondExp.symm

/-- Helper for Exercise 19.6.1: in discrete time, bounded measurable future-path functionals admit
the standard Markov conditional-expectation formula along `generatedFiltrationSpace X k`. -/
private theorem natFuturePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    (MeasureTheory.condExp (m := generatedFiltrationSpace X k) (P x : Measure Ω)
        (fun ω ↦ g (natFuturePath X k ω))) =ᵐ[(P x : Measure Ω)]
      (fun ω ↦ ∫ y, g y ∂κ (X k ω)) := by
  -- Proof comment: the Chapter 20 nat-indexed support theorem already proves the deterministic
  -- future-path conditional-expectation formula, and `natFuturePath` is the same shifted path.
  simpa [natFuturePath, shiftedPath] using
    (futurePathCondExp_of_markovProcessNat
      (X := X) (P := P) (κ := κ) (hX_meas := hX_meas) (hX0 := hX0) (hpath := hpath)
      (x := x) (k := k) (g := g) hg_meas hg_bdd)

/- Layering for Exercise 19.6.1:
- `source-facing`: a one-sided nearest-neighbor environment on `ℕ`, the blocked-at-zero
  transition matrix it determines, and the three sign-of-`E[log ρ₀]` state-classification
  conclusions for quenched realizations of that half-line walk.
- `core/canonical`: the Chapter 17 state predicates `IsTransientState`, `IsNullRecurrentState`,
  and `IsPositiveRecurrentState`.
- `bridge/view`: the one-ray conductance presentation of the blocked walk and the Chapter 20
  path-space oscillation bridge used in the critical regime. -/

/-- A one-sided nearest-neighbor environment on `ℕ`, assigning to each site the probability of a
jump to the right. The complementary mass is the left-jump probability away from the boundary, and
at `0` it becomes the blocked self-loop mass. -/
structure HalfLineRandomEnvironment where
  /-- The probability of a jump from `n` to `n + 1`. -/
  rightJumpProb : ℕ → ℝ≥0
  /-- The right-jump probabilities are at most `1`. -/
  rightJumpProb_le_one : ∀ n : ℕ, rightJumpProb n ≤ 1

namespace HalfLineRandomEnvironment

/-- A one-sided environment is elliptic if every right-jump probability lies strictly between `0`
and `1`. -/
class IsElliptic (W : HalfLineRandomEnvironment) : Prop where
  pos_lt_one (n : ℕ) : 0 < W.rightJumpProb n ∧ W.rightJumpProb n < 1

/-- In an elliptic one-sided environment, every right-jump probability is positive. -/
theorem IsElliptic.pos {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    0 < W.rightJumpProb n :=
  (hW.pos_lt_one n).1

/-- In an elliptic one-sided environment, every right-jump probability is strictly less than `1`.
-/
theorem IsElliptic.lt_one {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    W.rightJumpProb n < 1 :=
  (hW.pos_lt_one n).2

end HalfLineRandomEnvironment

/-- The logarithmic local Solomon ratio `log ρ_n` for a sampled one-sided environment. -/
def halfLineRandomEnvironmentLogRatio (W : Ω → HalfLineRandomEnvironment) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    Real.log
      (((((1 : ℝ≥0) - ((W ω).rightJumpProb n)) / ((W ω).rightJumpProb n) : ℝ≥0) : ℝ))

scoped[ProbabilityTheory] notation "logρ₊[" W "](" n ")" => halfLineRandomEnvironmentLogRatio W n

/-- A Solomon environment law on the half-line is a random nearest-neighbor environment on `ℕ`
whose log-ratio field is i.i.d. and whose sampled environments are almost surely elliptic. -/
class IsHalfLineSolomonEnvironmentLaw (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → HalfLineRandomEnvironment) : Prop where
  ae_elliptic : ∀ᵐ ω ∂μ, (W ω).IsElliptic
  logRatio_iid : IsIID (fun n ↦ logρ₊[W](n)) μ

namespace IsHalfLineSolomonEnvironmentLaw

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → HalfLineRandomEnvironment}

/-- In a half-line Solomon environment law, the sampled environment is elliptic almost surely. -/
theorem ae_elliptic_at (hW : IsHalfLineSolomonEnvironmentLaw μ W) (n : ℕ) :
    ∀ᵐ ω ∂μ, 0 < (W ω).rightJumpProb n ∧ (W ω).rightJumpProb n < 1 :=
  hW.ae_elliptic.mono fun _ hω ↦ hω.pos_lt_one n

/-- Helper for Exercise 19.6.1: the half-line i.i.d. log-ratio field gives identical
distribution between any two nonnegative coordinates. -/
theorem identDistrib_logRatio (hW : IsHalfLineSolomonEnvironmentLaw μ W) (m n : ℕ) :
    IdentDistrib (logρ₊[W](m)) (logρ₊[W](n)) μ μ :=
  hW.logRatio_iid.identDistrib m n

/-- Helper for Exercise 19.6.1: integrability of `logρ₊[W](0)` propagates to every nonnegative
coordinate of the half-line field. -/
theorem integrable_logRatio
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ₊[W](0)) μ) (n : ℕ) :
    Integrable (logρ₊[W](n)) μ := by
  -- Proof comment: identical distribution transports integrability from the origin to site `n`.
  simpa using (hW.identDistrib_logRatio n 0).symm.integrable_snd hlog

end IsHalfLineSolomonEnvironmentLaw

/-- The half-line RWRE transition matrix attached to a fixed environment `W`, with the boundary
attempt to jump left from `0` blocked so that the chain stays at `0`. -/
def blockedAtZeroRandomEnvironmentTransitionMatrix
    (W : HalfLineRandomEnvironment) : ℕ → ℕ → ℝ≥0∞
  | 0, m =>
      if m = 0 then (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞)
      else if m = 1 then W.rightJumpProb 0
      else 0
  | n + 1, m =>
      if m = n then (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)
      else if m = n + 2 then W.rightJumpProb (n + 1)
      else 0

/-- At `0`, the blocked half-line RWRE keeps the forbidden left-jump mass as a self-loop. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self (W : HalfLineRandomEnvironment) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W 0 0 =
      (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞) := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

/-- At `0`, the blocked half-line RWRE keeps the original right-jump probability. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one (W : HalfLineRandomEnvironment) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W 0 1 = W.rightJumpProb 0 := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

/-- Away from the boundary, the blocked half-line RWRE has the expected nearest-neighbor row. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_succ
    (W : HalfLineRandomEnvironment) (n m : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) m =
      if m = n then (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)
      else if m = n + 2 then W.rightJumpProb (n + 1)
      else 0 := rfl

/-- At an interior state `n + 1`, the blocked half-line RWRE jumps left to `n` with the owner
left-jump probability. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_left
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) n =
      (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞) := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

/-- At an interior state `n + 1`, the blocked half-line RWRE jumps right to `n + 2` with the
owner right-jump probability. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_right
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) (n + 2) =
      W.rightJumpProb (n + 1) := by
  simp [blockedAtZeroRandomEnvironmentTransitionMatrix]

-- Proof sketch: the boundary row is supported only at `0` and `1`. Every interior row `n + 1`
-- is supported only at `n` and `n + 2`, and those two masses add up to `1`.
/-- The blocked-at-zero half-line RWRE transition matrix is stochastic. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic (W : HalfLineRandomEnvironment) :
    IsStochasticMatrix (blockedAtZeroRandomEnvironmentTransitionMatrix W) := by
  intro x
  classical
  cases x with
  | zero =>
      have hsupport :
          ∀ y ∉ ({0, 1} : Finset ℕ), blockedAtZeroRandomEnvironmentTransitionMatrix W 0 y = 0 := by
        intro y hy
        have hy_zero : y ≠ 0 := by
          intro h
          exact hy (by simp [h])
        have hy_one : y ≠ 1 := by
          intro h
          exact hy (by simp [h])
        simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hy_zero, hy_one]
      rw [tsum_eq_sum hsupport]
      have hprob : (W.rightJumpProb 0 : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast W.rightJumpProb_le_one 0
      simpa [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self,
        blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one, add_comm] using
        add_tsub_cancel_of_le hprob
  | succ n =>
      have hsupport :
          ∀ y ∉ ({n, n + 2} : Finset ℕ),
            blockedAtZeroRandomEnvironmentTransitionMatrix W (n + 1) y = 0 := by
        intro y hy
        have hy_left : y ≠ n := by
          intro h
          exact hy (by simp [h])
        have hy_right : y ≠ n + 2 := by
          intro h
          exact hy (by simp [h])
        simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hy_left, hy_right]
      rw [tsum_eq_sum hsupport]
      have hprob : (W.rightJumpProb (n + 1) : ℝ≥0∞) ≤ 1 := by
        exact_mod_cast W.rightJumpProb_le_one (n + 1)
      simpa [blockedAtZeroRandomEnvironmentTransitionMatrix_left,
        blockedAtZeroRandomEnvironmentTransitionMatrix_right, add_comm] using
        add_tsub_cancel_of_le hprob

/-- The discrete kernel attached to the blocked-at-zero half-line RWRE transition matrix is
Markov. -/
instance (W : HalfLineRandomEnvironment) :
    IsMarkovKernel (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) :=
  discreteMatrixKernel_isMarkovKernel _
    (blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic W)

/-- Helper for Exercise 19.6.1: from any state `n`, the blocked half-line kernel keeps the owner
right-jump probability on the edge `n ⟶ n + 1`. -/
theorem blockedAtZeroRandomEnvironmentTransitionMatrix_forward
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W n (n + 1) =
      W.rightJumpProb n := by
  cases n with
  | zero =>
      simpa using blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one W
  | succ n =>
      simpa [Nat.add_assoc] using blockedAtZeroRandomEnvironmentTransitionMatrix_right W n

/-- Helper for Exercise 19.6.1: the conductance on the edge `{n, n + 1}` of the blocked
half-line walk is obtained recursively by dividing by the local left/right ratio at the next
site. -/
def blockedAtZeroEdgeConductance (W : HalfLineRandomEnvironment) : ℕ → ℝ≥0∞
  | 0 => W.rightJumpProb 0
  | n + 1 =>
      blockedAtZeroEdgeConductance W n /
        ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)))

/-- Helper for Exercise 19.6.1: the boundary edge conductance is the right-jump probability at
`0`. -/
@[simp]
theorem blockedAtZeroEdgeConductance_zero (W : HalfLineRandomEnvironment) :
    blockedAtZeroEdgeConductance W 0 = W.rightJumpProb 0 := rfl

/-- Helper for Exercise 19.6.1: successive edge conductances satisfy the local
`q_{n+1} / p_{n+1}` recursion. -/
@[simp]
theorem blockedAtZeroEdgeConductance_succ (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroEdgeConductance W (n + 1) =
      blockedAtZeroEdgeConductance W n /
        ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1))) := rfl

/-- Helper for Exercise 19.6.1: in an elliptic environment, the local blocked half-line ratio
`((1 - p_{n+1}) / p_{n+1})` is strictly positive. -/
theorem blockedAtZeroLocalRatio_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    0 < (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) := by
  have hnum : 0 < ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) := by
    exact_mod_cast (tsub_pos_iff_lt.2 (hW.lt_one (n + 1)))
  -- Proof comment: both the left-jump and right-jump factors are strictly positive.
  exact (ENNReal.div_pos_iff).2 ⟨hnum.ne', by simp⟩

/-- Helper for Exercise 19.6.1: in an elliptic environment, the local blocked half-line ratio is
finite. -/
theorem blockedAtZeroLocalRatio_ne_top
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) ≠ ∞ := by
  have hnum : ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) ≠ ∞ := by
    exact ENNReal.sub_ne_top (by simp)
  -- Proof comment: the numerator is finite and the right-jump probability is strictly positive.
  exact ENNReal.div_ne_top hnum (by exact_mod_cast (hW.pos (n + 1)).ne')

/-- Helper for Exercise 19.6.1: ellipticity keeps every blocked half-line edge conductance
strictly positive. -/
theorem blockedAtZeroEdgeConductance_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    0 < blockedAtZeroEdgeConductance W n := by
  induction n with
  | zero =>
      -- Proof comment: the boundary edge conductance is the positive right-jump probability.
      simpa using (show 0 < (W.rightJumpProb 0 : ℝ≥0∞) by exact_mod_cast hW.pos 0)
  | succ n ih =>
      -- Proof comment: the recursion divides a positive conductance by a finite local ratio.
      rw [blockedAtZeroEdgeConductance_succ, div_eq_mul_inv]
      exact ENNReal.mul_pos (ne_of_gt ih)
        (ne_of_gt ((ENNReal.inv_pos).2 (blockedAtZeroLocalRatio_ne_top hW n)))

/-- Helper for Exercise 19.6.1: ellipticity keeps every blocked half-line edge conductance
finite. -/
theorem blockedAtZeroEdgeConductance_ne_top
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    blockedAtZeroEdgeConductance W n ≠ ∞ := by
  induction n with
  | zero =>
      -- Proof comment: the boundary conductance is an `ℝ≥0`-valued probability and hence
      -- finite.
      simp [blockedAtZeroEdgeConductance]
  | succ n ih =>
      -- Proof comment: the recursion divides a finite conductance by a strictly positive local
      -- ratio, so the result stays finite.
      rw [blockedAtZeroEdgeConductance_succ, div_eq_mul_inv]
      exact ENNReal.mul_ne_top ih
        ((ENNReal.inv_ne_top).2 (ne_of_gt (blockedAtZeroLocalRatio_pos hW n)))

/-- Helper for Exercise 19.6.1: neighboring blocked half-line edge conductances differ by the
local ratio `((1 - p_{n+1}) / p_{n+1})`. -/
theorem blockedAtZeroEdgeConductance_ratio
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    blockedAtZeroEdgeConductance W n =
      (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
        blockedAtZeroEdgeConductance W (n + 1) := by
  let r : ℝ≥0∞ := (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1))
  have hr_ne_zero : r ≠ 0 := ne_of_gt (blockedAtZeroLocalRatio_pos hW n)
  have hr_ne_top : r ≠ ∞ := blockedAtZeroLocalRatio_ne_top hW n
  -- Proof comment: multiply the successor recursion by the local ratio and cancel `r * r⁻¹`.
  calc
    blockedAtZeroEdgeConductance W n
        = blockedAtZeroEdgeConductance W n * (r * r⁻¹) := by
            rw [ENNReal.mul_inv_cancel hr_ne_zero hr_ne_top, mul_one]
    _ = r * (blockedAtZeroEdgeConductance W n * r⁻¹) := by ac_rfl
    _ = r * blockedAtZeroEdgeConductance W (n + 1) := by
          rw [blockedAtZeroEdgeConductance_succ, div_eq_mul_inv]

/-- Helper for Exercise 19.6.1: multiplying the local blocked half-line ratio by the
right-jump probability recovers the left-jump probability. -/
theorem blockedAtZeroLocalRatio_mul_rightJumpProb
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
        W.rightJumpProb (n + 1) =
      (1 : ℝ≥0∞) - W.rightJumpProb (n + 1) := by
  -- Proof comment: cancel the positive denominator in the local ratio definition.
  exact ENNReal.div_mul_cancel (by exact_mod_cast (hW.pos (n + 1)).ne') (by simp)

/-- Helper for Exercise 19.6.1: the symmetric conductance family whose normalized walk is the
blocked half-line RWRE. The edge `{n, n + 1}` carries `blockedAtZeroEdgeConductance W n`, and
the blocked self-loop at `0` carries the left-jump mass `1 - p₀`. -/
def blockedAtZeroConductance (W : HalfLineRandomEnvironment) : ℕ → ℕ → ℝ≥0∞
  | 0, 0 => (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞)
  | n, m =>
      if m = n + 1 then blockedAtZeroEdgeConductance W n
      else if n = m + 1 then blockedAtZeroEdgeConductance W m
      else 0

/-- Helper for Exercise 19.6.1: the blocked conductance at the boundary self-loop is exactly the
blocked left-jump mass. -/
theorem blockedAtZeroConductance_zero_self (W : HalfLineRandomEnvironment) :
    blockedAtZeroConductance W 0 0 =
      (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞) := rfl

/-- Helper for Exercise 19.6.1: the blocked conductance on the edge `{n, n + 1}` is the
associated edge conductance. -/
theorem blockedAtZeroConductance_forward
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroConductance W n (n + 1) = blockedAtZeroEdgeConductance W n := by
  cases n with
  | zero =>
      simp [blockedAtZeroConductance]
  | succ n =>
      simp [blockedAtZeroConductance]

/-- Helper for Exercise 19.6.1: every interior blocked conductance row has the canonical
two-neighbor normal form. -/
theorem blockedAtZeroConductance_succ_apply
    (W : HalfLineRandomEnvironment) (n y : ℕ) :
    blockedAtZeroConductance W (n + 1) y =
      if y = n + 2 then blockedAtZeroEdgeConductance W (n + 1)
      else if y = n then blockedAtZeroEdgeConductance W n
      else 0 := by
  -- Proof comment: rewrite the raw definition once into the stable `y = n` / `y = n + 2`
  -- spelling used by every later interior-row argument.
  by_cases hy_right : y = n + 2
  · subst hy_right
    simp [blockedAtZeroConductance]
  · by_cases hy_left : y = n
    · subst hy_left
      simp [blockedAtZeroConductance, hy_right]
    · have hback : n + 1 ≠ y + 1 := by
        omega
      have hy_left' : n ≠ y := by
        omega
      simp [blockedAtZeroConductance, hy_right, hy_left, hy_left']

/-- Helper for Exercise 19.6.1: the blocked conductance on the reversed edge `{n + 1, n}` is the
same edge conductance. -/
theorem blockedAtZeroConductance_backward
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    blockedAtZeroConductance W (n + 1) n = blockedAtZeroEdgeConductance W n := by
  -- Proof comment: the new interior-row normal form exposes the backward edge directly.
  simpa [blockedAtZeroConductance_succ_apply]

/-- Helper for Exercise 19.6.1: the blocked conductance family is symmetric. -/
theorem blockedAtZeroConductance_symmetric
    (W : HalfLineRandomEnvironment) (x y : ℕ) :
    blockedAtZeroConductance W x y = blockedAtZeroConductance W y x := by
  cases x with
  | zero =>
      cases y with
      | zero =>
          simp [blockedAtZeroConductance]
      | succ y =>
          simp [blockedAtZeroConductance]
  | succ x =>
      cases y with
      | zero =>
          simp [blockedAtZeroConductance]
      | succ y =>
          by_cases hxy : y = x + 1
          · subst hxy
            simp [blockedAtZeroConductance]
          · by_cases hyx : x = y + 1
            · subst hyx
              simp [blockedAtZeroConductance]
            · simp [blockedAtZeroConductance, hxy, hyx]

/-- Helper for Exercise 19.6.1: the blocked conductance row weight at `0` is `1`. -/
theorem blockedAtZeroConductance_vertexWeight_zero (W : HalfLineRandomEnvironment) :
    conductance (blockedAtZeroConductance W) 0 = 1 := by
  classical
  have hsupport :
      ∀ y ∉ ({0, 1} : Finset ℕ), blockedAtZeroConductance W 0 y = 0 := by
    intro y hy
    have hy_zero : y ≠ 0 := by
      intro hy'
      exact hy (by simp [hy'])
    have hy_one : y ≠ 1 := by
      intro hy'
      exact hy (by simp [hy'])
    simp [blockedAtZeroConductance, hy_zero, hy_one]
  rw [conductance, tsum_eq_sum hsupport]
  have hprob : (W.rightJumpProb 0 : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast W.rightJumpProb_le_one 0
  -- Proof comment: the two boundary row weights are the blocked left-jump mass and the original
  -- right-jump mass, so they add to `1`.
  simpa [blockedAtZeroConductance_zero_self, blockedAtZeroConductance_forward,
    blockedAtZeroEdgeConductance_zero, add_comm] using
    (add_tsub_cancel_of_le hprob :
      W.rightJumpProb 0 + ((1 : ℝ≥0∞) - W.rightJumpProb 0) = 1)

/-- Helper for Exercise 19.6.1: the blocked conductance row weight at `n + 1` is the sum of the
two adjacent edge conductances. -/
theorem blockedAtZeroConductance_vertexWeight_succ
    (W : HalfLineRandomEnvironment) (n : ℕ) :
    conductance (blockedAtZeroConductance W) (n + 1) =
      blockedAtZeroEdgeConductance W n + blockedAtZeroEdgeConductance W (n + 1) := by
  classical
  have hsupport :
      ∀ y ∉ ({n, n + 2} : Finset ℕ), blockedAtZeroConductance W (n + 1) y = 0 := by
    intro y hy
    have hy_left : y ≠ n := by
      intro hy'
      exact hy (by simp [hy'])
    have hy_right : y ≠ n + 2 := by
      intro hy'
      exact hy (by simp [hy'])
    -- Proof comment: off the two neighbors, the interior row-normal form is identically zero.
    rw [blockedAtZeroConductance_succ_apply]
    simp [hy_left, hy_right]
  rw [conductance, tsum_eq_sum hsupport]
  -- Proof comment: only the two neighboring edge conductances survive in the row sum.
  simp [blockedAtZeroConductance_succ_apply]

/-- Helper for Exercise 19.6.1: under ellipticity, row-normalizing the blocked conductance family
recovers the blocked half-line RWRE transition matrix. -/
theorem blockedAtZeroTransition_eq_conductanceTransitionMatrix
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (x y : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W x y =
      conductanceTransitionMatrix (blockedAtZeroConductance W) x y := by
  cases x with
  | zero =>
      cases y with
      | zero =>
          rw [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self,
            conductanceTransitionMatrix_apply, blockedAtZeroConductance_zero_self,
            blockedAtZeroConductance_vertexWeight_zero]
          simp
      | succ y =>
          cases y with
          | zero =>
              rw [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one,
                conductanceTransitionMatrix_apply, blockedAtZeroConductance_forward,
                blockedAtZeroConductance_vertexWeight_zero]
              simp [blockedAtZeroEdgeConductance_zero]
          | succ y =>
              simp [blockedAtZeroRandomEnvironmentTransitionMatrix, conductanceTransitionMatrix_apply,
                blockedAtZeroConductance, blockedAtZeroConductance_vertexWeight_zero]
  | succ n =>
      -- Route correction: work entirely in the canonical interior-row normal form instead of
      -- rediscovering the backward/off-support cases from the raw conductance definition.
      have hden_pos : 0 < conductance (blockedAtZeroConductance W) (n + 1) := by
        -- Proof comment: the row weight contains the positive left-edge conductance.
        rw [blockedAtZeroConductance_vertexWeight_succ]
        exact lt_of_lt_of_le (blockedAtZeroEdgeConductance_pos hW n)
          (le_add_of_nonneg_right (zero_le _))
      have hden_ne_zero : conductance (blockedAtZeroConductance W) (n + 1) ≠ 0 := ne_of_gt hden_pos
      have hden_ne_top : conductance (blockedAtZeroConductance W) (n + 1) ≠ ∞ := by
        -- Proof comment: both adjacent edge conductances are finite in an elliptic environment.
        rw [blockedAtZeroConductance_vertexWeight_succ]
        exact (ENNReal.add_ne_top).2
          ⟨blockedAtZeroEdgeConductance_ne_top hW n,
            blockedAtZeroEdgeConductance_ne_top hW (n + 1)⟩
      by_cases hy_right : y = n + 2
      · subst hy_right
        have hprob : (W.rightJumpProb (n + 1) : ℝ≥0∞) ≤ 1 := by
          exact_mod_cast W.rightJumpProb_le_one (n + 1)
        have hsum :
            ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) + W.rightJumpProb (n + 1) = 1 := by
          simpa [add_comm] using
            (add_tsub_cancel_of_le hprob :
              W.rightJumpProb (n + 1) + ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) = 1)
        have hmul :
            conductance (blockedAtZeroConductance W) (n + 1) * W.rightJumpProb (n + 1) =
              blockedAtZeroEdgeConductance W (n + 1) := by
          calc
            conductance (blockedAtZeroConductance W) (n + 1) * W.rightJumpProb (n + 1)
                = (blockedAtZeroEdgeConductance W n +
                    blockedAtZeroEdgeConductance W (n + 1)) * W.rightJumpProb (n + 1) := by
                      rw [blockedAtZeroConductance_vertexWeight_succ]
            _ = blockedAtZeroEdgeConductance W n * W.rightJumpProb (n + 1) +
                  blockedAtZeroEdgeConductance W (n + 1) * W.rightJumpProb (n + 1) := by
                    rw [add_mul]
            _ = ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
                    blockedAtZeroEdgeConductance W (n + 1)) * W.rightJumpProb (n + 1) +
                  blockedAtZeroEdgeConductance W (n + 1) * W.rightJumpProb (n + 1) := by
                    rw [blockedAtZeroEdgeConductance_ratio hW n]
            _ = ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
                    W.rightJumpProb (n + 1)) * blockedAtZeroEdgeConductance W (n + 1) +
                  W.rightJumpProb (n + 1) * blockedAtZeroEdgeConductance W (n + 1) := by
                    ac_rfl
            _ = (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) *
                    blockedAtZeroEdgeConductance W (n + 1)) +
                  W.rightJumpProb (n + 1) * blockedAtZeroEdgeConductance W (n + 1) := by
                    rw [blockedAtZeroLocalRatio_mul_rightJumpProb hW n]
            _ = (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) + W.rightJumpProb (n + 1)) *
                  blockedAtZeroEdgeConductance W (n + 1) := by
                    rw [add_mul]
            _ = blockedAtZeroEdgeConductance W (n + 1) := by
                  rw [hsum, one_mul]
        rw [blockedAtZeroRandomEnvironmentTransitionMatrix_right, conductanceTransitionMatrix_apply,
          blockedAtZeroConductance_forward]
        have hdiv :
            blockedAtZeroEdgeConductance W (n + 1) /
                conductance (blockedAtZeroConductance W) (n + 1) =
              W.rightJumpProb (n + 1) / 1 := by
          exact
            (ENNReal.div_eq_div_iff
              (a := (1 : ℝ≥0∞))
              (b := conductance (blockedAtZeroConductance W) (n + 1))
              (c := blockedAtZeroEdgeConductance W (n + 1))
              (d := W.rightJumpProb (n + 1))
              (by simp) (by simp) hden_ne_zero hden_ne_top).2
              (by simpa [one_mul] using hmul.symm)
        simpa using hdiv.symm
      · by_cases hy_left : y = n
        · subst y
          have hprob : (W.rightJumpProb (n + 1) : ℝ≥0∞) ≤ 1 := by
            exact_mod_cast W.rightJumpProb_le_one (n + 1)
          have hsum :
              ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) + W.rightJumpProb (n + 1) = 1 := by
            simpa [add_comm] using
              (add_tsub_cancel_of_le hprob :
                W.rightJumpProb (n + 1) + ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) = 1)
          have hmulRight :
              conductance (blockedAtZeroConductance W) (n + 1) * W.rightJumpProb (n + 1) =
                blockedAtZeroEdgeConductance W (n + 1) := by
            calc
              conductance (blockedAtZeroConductance W) (n + 1) * W.rightJumpProb (n + 1)
                  = (blockedAtZeroEdgeConductance W n +
                      blockedAtZeroEdgeConductance W (n + 1)) * W.rightJumpProb (n + 1) := by
                        rw [blockedAtZeroConductance_vertexWeight_succ]
              _ = blockedAtZeroEdgeConductance W n * W.rightJumpProb (n + 1) +
                    blockedAtZeroEdgeConductance W (n + 1) * W.rightJumpProb (n + 1) := by
                      rw [add_mul]
              _ = ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
                      blockedAtZeroEdgeConductance W (n + 1)) * W.rightJumpProb (n + 1) +
                    blockedAtZeroEdgeConductance W (n + 1) * W.rightJumpProb (n + 1) := by
                      rw [blockedAtZeroEdgeConductance_ratio hW n]
              _ = ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
                      W.rightJumpProb (n + 1)) * blockedAtZeroEdgeConductance W (n + 1) +
                    W.rightJumpProb (n + 1) * blockedAtZeroEdgeConductance W (n + 1) := by
                      ac_rfl
              _ = (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) *
                      blockedAtZeroEdgeConductance W (n + 1)) +
                    W.rightJumpProb (n + 1) * blockedAtZeroEdgeConductance W (n + 1) := by
                      rw [blockedAtZeroLocalRatio_mul_rightJumpProb hW n]
              _ = (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) + W.rightJumpProb (n + 1)) *
                    blockedAtZeroEdgeConductance W (n + 1) := by
                      rw [add_mul]
              _ = blockedAtZeroEdgeConductance W (n + 1) := by
                    rw [hsum, one_mul]
          have hmul :
              conductance (blockedAtZeroConductance W) (n + 1) *
                  ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) =
                blockedAtZeroEdgeConductance W n := by
            calc
              conductance (blockedAtZeroConductance W) (n + 1) *
                  ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1))
                  = conductance (blockedAtZeroConductance W) (n + 1) *
                      ((((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) /
                        W.rightJumpProb (n + 1)) * W.rightJumpProb (n + 1)) := by
                          rw [blockedAtZeroLocalRatio_mul_rightJumpProb hW n]
              _ = (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
                    (conductance (blockedAtZeroConductance W) (n + 1) *
                      W.rightJumpProb (n + 1)) := by
                        ac_rfl
              _ = (((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / W.rightJumpProb (n + 1)) *
                    blockedAtZeroEdgeConductance W (n + 1) := by
                        rw [hmulRight]
              _ = blockedAtZeroEdgeConductance W n := by
                    rw [blockedAtZeroEdgeConductance_ratio hW n]
          rw [blockedAtZeroRandomEnvironmentTransitionMatrix_left, conductanceTransitionMatrix_apply,
            blockedAtZeroConductance_backward]
          have hdiv :
              blockedAtZeroEdgeConductance W n /
                  conductance (blockedAtZeroConductance W) (n + 1) =
                ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) / 1 := by
            exact
              (ENNReal.div_eq_div_iff
                (a := (1 : ℝ≥0∞))
                (b := conductance (blockedAtZeroConductance W) (n + 1))
                (c := blockedAtZeroEdgeConductance W n)
                (d := (1 : ℝ≥0∞) - W.rightJumpProb (n + 1))
                (by simp) (by simp) hden_ne_zero hden_ne_top).2
              (by simpa [one_mul] using hmul.symm)
          simpa using hdiv.symm
        · -- Proof comment: away from the two neighbors `n` and `n + 2`, both kernels vanish.
          simp [blockedAtZeroRandomEnvironmentTransitionMatrix_succ,
            conductanceTransitionMatrix_apply, blockedAtZeroConductance_succ_apply,
            hy_right, hy_left]

/-- Helper for Exercise 19.6.1: the blocked half-line transition matrix is a random walk with
weights given by the one-ray conductance family. -/
theorem blockedAtZero_isRandomWalkWithWeights
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) :
    IsRandomWalkWithWeights
      (blockedAtZeroRandomEnvironmentTransitionMatrix W) (blockedAtZeroConductance W) where
  isStochastic := blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic W
  symmetric := blockedAtZeroConductance_symmetric W
  transition_eq := by
    intro x y
    -- Proof comment: the blocked kernel is exactly the normalized blocked conductance walk.
    simpa [conductanceTransitionMatrix_apply] using
      blockedAtZeroTransition_eq_conductanceTransitionMatrix hW x y

/-- Helper for Exercise 19.6.1: under ellipticity, a realization of the blocked half-line kernel
is also a realization of its conductance-walk presentation. -/
theorem isMarkovProcessRealization_blockedAtZeroConductance
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) P X]
    (hW : W.IsElliptic) :
    IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (conductanceTransitionMatrix (blockedAtZeroConductance W)) ^ n)
      P X := by
  have htransition :
      blockedAtZeroRandomEnvironmentTransitionMatrix W =
        conductanceTransitionMatrix (blockedAtZeroConductance W) := by
    funext x y
    exact blockedAtZeroTransition_eq_conductanceTransitionMatrix hW x y
  -- Proof comment: the realization owner transports across the pointwise equality of the two
  -- one-step transition matrices.
  simpa [htransition] using
    (inferInstance :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X)

/-- Helper for Exercise 19.6.1: composing a positive `n`-step singleton mass with a positive
one-step singleton mass yields a positive `(n + 1)`-step singleton mass for the blocked kernel. -/
private theorem blockedAtZeroKernel_singleton_pos_succ
    {W : HalfLineRandomEnvironment} {x y z : ℕ} {n : ℕ}
    (hxy : 0 <
      ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x)
        ({y} : Set ℕ))
    (hyz : 0 <
      (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) y
        ({z} : Set ℕ)) :
    0 <
      ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ (n + 1)) x)
        ({z} : Set ℕ) := by
  let κ := discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)
  have hmeas : Measurable fun w : ℕ ↦ κ w ({z} : Set ℕ) :=
    Kernel.measurable_coe κ (MeasurableSet.singleton z)
  have hySupport : y ∈ Function.support fun w : ℕ ↦ κ w ({z} : Set ℕ) := by
    change (κ y) ({z} : Set ℕ) ≠ 0
    exact ne_of_gt hyz
  have hsupportPos :
      0 < ((κ ^ n) x) (Function.support fun w : ℕ ↦ κ w ({z} : Set ℕ)) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the composition integral is positive because the intermediate state `y`
  -- already lies in the support of the one-step kernel toward `z`.
  rw [Kernel.pow_succ_apply_eq_lintegral κ n x (measurableSet_singleton z)]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Exercise 19.6.1: following `n` successive right jumps from `x` has strictly
positive `n`-step mass in an elliptic blocked half-line environment. -/
theorem blockedAtZeroRightPathMass_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (x : ℕ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x)
          ({x + n} : Set ℕ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: the zero-step kernel is the identity and charges the start state with mass
      -- `1`.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x)
              ({x + n} : Set ℕ) := ih x
      have hlast :
          0 <
            (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) (x + n)
              ({x + (n + 1)} : Set ℕ) := by
        rw [discreteMatrixKernel_apply_singleton]
        -- Proof comment: the final step is the forward edge from `x + n` to `x + n + 1`.
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (show
            0 <
              blockedAtZeroRandomEnvironmentTransitionMatrix W (x + n) ((x + n) + 1) by
              rw [blockedAtZeroRandomEnvironmentTransitionMatrix_forward]
              exact_mod_cast hW.pos (x + n))
      exact blockedAtZeroKernel_singleton_pos_succ hrest hlast

/-- Helper for Exercise 19.6.1: following `n` successive left jumps from `x + n` down to `x` has
strictly positive `n`-step mass in an elliptic blocked half-line environment. -/
theorem blockedAtZeroLeftPathMass_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (x : ℕ) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) (x + n))
          ({x} : Set ℕ) := by
  intro n
  induction n generalizing x with
  | zero =>
      -- Proof comment: time `0` again puts all mass at the starting state.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id x) ({x} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hrest :
          0 <
            ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
              ((x + 1) + n)) ({x + 1} : Set ℕ) := by
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (x + 1)
      have hleftprob : 0 < ((1 : ℝ≥0) - W.rightJumpProb (x + 1) : ℝ≥0) := by
        exact tsub_pos_iff_lt.2 (hW.lt_one (x + 1))
      have hlast :
          0 <
            (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) (x + 1)
              ({x} : Set ℕ) := by
        rw [discreteMatrixKernel_apply_singleton,
          blockedAtZeroRandomEnvironmentTransitionMatrix_left]
        simpa [ENNReal.coe_sub] using hleftprob
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (blockedAtZeroKernel_singleton_pos_succ (W := W) hrest hlast)

/-- Helper for Exercise 19.6.1: staying at the blocked boundary state `0` for any prescribed
number of steps has strictly positive mass, because the forbidden left jump was turned into a
positive self-loop. -/
theorem blockedAtZeroZeroPathMass_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) :
    ∀ n : ℕ,
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) 0)
          ({0} : Set ℕ) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: at time `0`, the kernel is the identity and charges the start state with
      -- mass `1`.
      rw [pow_zero]
      simpa using
        (show 0 < (Kernel.id 0) ({0} : Set ℕ) by
          rw [Kernel.id_apply]
          simp)
  | succ n ih =>
      have hself :
          0 <
            (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0
              ({0} : Set ℕ) := by
        rw [discreteMatrixKernel_apply_singleton,
          blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self]
        exact_mod_cast (tsub_pos_iff_lt.2 (hW.lt_one 0))
      -- Proof comment: append one more positive self-loop at `0` to the already positive
      -- `n`-step stay-put path.
      simpa using blockedAtZeroKernel_singleton_pos_succ (W := W) ih hself

/-- Helper for Exercise 19.6.1: from any interior point `x ∈ {1, ..., N}`, the blocked walk can
hit `0` exactly at time `N` by first following the monotone left path to `0` and then using the
positive self-loop at the boundary for the remaining steps. -/
theorem blockedAtZeroPrefixHitsZeroAtTime_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) {x N : ℕ}
    (hx1 : 1 ≤ x) (hxN : x ≤ N) :
    0 <
      ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ N) x)
        ({0} : Set ℕ) := by
  let m : ℕ := N - x
  have hleft :
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ x) x)
          ({0} : Set ℕ) := by
    simpa [Nat.zero_add] using blockedAtZeroLeftPathMass_pos (W := W) hW 0 x
  have hm :
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ (x + m)) x)
          ({0} : Set ℕ) := by
    -- Proof comment: each extra step after the monotone descent is realized by the positive
    -- self-loop at `0`.
    induction m with
    | zero =>
        simpa using hleft
    | succ m ihm =>
        have hself :
            0 <
              (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0
                ({0} : Set ℕ) := by
          rw [discreteMatrixKernel_apply_singleton,
            blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self]
          exact_mod_cast (tsub_pos_iff_lt.2 (hW.lt_one 0))
        simpa [Nat.add_assoc] using blockedAtZeroKernel_singleton_pos_succ (W := W) ihm hself
  -- Proof comment: `x + (N - x) = N` reindexes the padded left-path mass to the target time.
  simpa [m, Nat.add_sub_of_le hxN] using hm

/-- Helper for Exercise 19.6.1: the blocked half-line kernel is irreducible under ellipticity,
because every target state can be reached by a monotone path of strictly positive mass. -/
theorem blockedAtZeroKernel_isIrreducible
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) :
    Kernel.IsIrreducible (Measure.count : Measure ℕ)
      (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) := by
  refine ⟨?_⟩
  intro A hA hcount x
  have hA_nonempty : A.Nonempty := by
    by_contra hA_empty
    simp [Set.not_nonempty_iff_eq_empty.mp hA_empty] at hcount
  rcases hA_nonempty with ⟨y, hyA⟩
  by_cases hxy : x ≤ y
  · let n : ℕ := y - x
    have hy' : y = x + n := by
      simpa [n] using (Nat.add_sub_of_le hxy).symm
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x)
            ({y} : Set ℕ) := by
      simpa [hy'] using blockedAtZeroRightPathMass_pos (W := W) hW x n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))
  · have hyx : y < x := lt_of_not_ge hxy
    let n : ℕ := x - y
    have hx' : x = y + n := by
      simpa [n] using (Nat.add_sub_of_le (le_of_lt hyx)).symm
    refine ⟨n, ?_⟩
    have hsingleton :
        0 <
          ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x)
            ({y} : Set ℕ) := by
      simpa [hx', Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        blockedAtZeroLeftPathMass_pos (W := W) hW y n
    exact lt_of_lt_of_le hsingleton (measure_mono (Set.singleton_subset_iff.mpr hyA))

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ]
variable {W : Ω → HalfLineRandomEnvironment}
variable {P : Ω → ℕ → ProbabilityMeasure Ξ} {X : Ω → ℕ → Ξ → ℕ}
variable (hW : IsHalfLineSolomonEnvironmentLaw μ W)
variable
  (hreal :
    ∀ ω,
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
        (P ω) (X ω))
variable (hlog : Integrable (logρ₊[W](0)) μ)

/-- Helper for Exercise 19.6.1: identify the path-space measurable structure on `Stream' ℝ` with
the product measurable structure on `ℕ → ℝ`. -/
local instance : MeasurableSpace (Stream' ℝ) :=
  inferInstanceAs (MeasurableSpace (ℕ → ℝ))

/-- Helper for Exercise 19.6.1: the one-sided shift on `Stream' ℝ` is measurable coordinatewise.
-/
private lemma measurableTailReal : Measurable (Stream'.tail : Stream' ℝ → Stream' ℝ) := by
  -- Proof comment: each output coordinate of the tail is the input coordinate one step later.
  exact measurable_pi_lambda _ fun i ↦ measurable_pi_apply (i + 1)

/-- Helper for Exercise 19.6.1: the path-space partial sums
`ω ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω` are measurable. -/
private lemma measurablePartialSumEvalZero (n : ℕ) :
    Measurable (fun ω : ℕ → ℝ ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω) := by
  -- Proof comment: reuse the Chapter 20 owner for measurable Birkhoff sums on shift path space.
  simpa using
    measurable_birkhoffSum (τ := Stream'.tail) (X₀ := Function.eval 0)
      measurableTailReal (measurable_pi_apply 0) n

/-- Helper for Exercise 19.6.1: a negative mean and the strong law force the partial sums of an
i.i.d. real field eventually below half the mean slope. -/
theorem ae_eventually_prefixSum_le_halfMean_mul_of_mean_neg
    {Y : ℕ → Ω → ℝ}
    (hint : Integrable (Y 0) μ)
    (hY_iid : IsIID Y μ)
    (hmean : ∫ ω, Y 0 ω ∂μ < 0) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω) ≤
            ((∫ ω, Y 0 ω ∂μ) / 2) * (n : ℝ)) atTop := by
  have hindep : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    intro i j hij
    exact hY_iid.iIndepFun.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦ hY_iid.identDistrib i 0
  have hslln := ProbabilityTheory.strong_law_ae_real Y hint hindep hident
  have hhalf : (∫ ω, Y 0 ω ∂μ) < (∫ ω, Y 0 ω ∂μ) / 2 := by
    linarith
  filter_upwards [hslln] with ω hω
  have hlt :
      ∀ᶠ n in atTop,
        (Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)) / (n : ℝ) <
          (∫ ω, Y 0 ω ∂μ) / 2 := by
    simpa using hω.eventually (Iio_mem_nhds hhalf)
  have hpos : Filter.Eventually (fun n : ℕ ↦ 0 < (n : ℝ)) atTop := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, fun n hn ↦ ?_⟩
    positivity
  -- Proof comment: once the empirical averages stay below `mean / 2`, multiply by the positive
  -- denominator `n`.
  filter_upwards [hlt, hpos] with n hn hn_pos
  exact le_of_lt ((div_lt_iff₀ hn_pos).mp hn)

/-- Helper for Exercise 19.6.1: a positive mean and the strong law force the partial sums of an
i.i.d. real field eventually above half the mean slope. -/
theorem ae_eventually_halfMean_mul_le_prefixSum_of_mean_pos
    {Y : ℕ → Ω → ℝ}
    (hint : Integrable (Y 0) μ)
    (hY_iid : IsIID Y μ)
    (hmean : 0 < ∫ ω, Y 0 ω ∂μ) :
    ∀ᵐ ω ∂μ,
      Filter.Eventually
        (fun n : ℕ ↦
          ((∫ ω, Y 0 ω ∂μ) / 2) * (n : ℝ) ≤
            Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)) atTop := by
  have hindep : Pairwise fun i j ↦ Y i ⟂ᵢ[μ] Y j := by
    intro i j hij
    exact hY_iid.iIndepFun.indepFun hij
  have hident : ∀ i, IdentDistrib (Y i) (Y 0) μ μ := fun i ↦ hY_iid.identDistrib i 0
  have hslln := ProbabilityTheory.strong_law_ae_real Y hint hindep hident
  have hhalf : (∫ ω, Y 0 ω ∂μ) / 2 < (∫ ω, Y 0 ω ∂μ) := by
    linarith
  filter_upwards [hslln] with ω hω
  have hlt :
      ∀ᶠ n in atTop,
        (∫ ω, Y 0 ω ∂μ) / 2 <
          (Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)) / (n : ℝ) := by
    simpa using hω.eventually (Ioi_mem_nhds hhalf)
  have hpos : Filter.Eventually (fun n : ℕ ↦ 0 < (n : ℝ)) atTop := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, fun n hn ↦ ?_⟩
    positivity
  -- Proof comment: multiply the eventual lower bound on the averages by the positive
  -- denominator `n`.
  filter_upwards [hlt, hpos] with n hn hn_pos
  exact le_of_lt ((lt_div_iff₀ hn_pos).mp hn)

/-- Helper for Exercise 19.6.1: in an elliptic sampled environment, the blocked local ratio
`((1 - p_{n+1}) / p_{n+1})` is the exponential of the half-line logarithmic ratio field. -/
theorem blockedAtZeroLocalRatio_eq_ofReal_exp_logRatio
    (ω : Ω) (hω : (W ω).IsElliptic) (n : ℕ) :
    (((1 : ℝ≥0∞) - (W ω).rightJumpProb (n + 1)) / (W ω).rightJumpProb (n + 1)) =
      ENNReal.ofReal (Real.exp (logρ₊[W](n + 1) ω)) := by
  let ratioNN : ℝ≥0 :=
    ((1 : ℝ≥0) - (W ω).rightJumpProb (n + 1)) / (W ω).rightJumpProb (n + 1)
  have hratio_pos : 0 < (ratioNN : ℝ) := by
    have hratioNN_pos : 0 < ratioNN := by
      exact div_pos (tsub_pos_iff_lt.2 (hω.lt_one (n + 1))) (hω.pos (n + 1))
    exact_mod_cast hratioNN_pos
  have hratio_exp : (ratioNN : ℝ) = Real.exp (logρ₊[W](n + 1) ω) := by
    -- Proof comment: the logarithmic ratio was defined from this positive real ratio.
    rw [halfLineRandomEnvironmentLogRatio, Real.exp_log hratio_pos]
  have hle : (W ω).rightJumpProb (n + 1) ≤ 1 := (W ω).rightJumpProb_le_one (n + 1)
  have hp : (W ω).rightJumpProb (n + 1) ≠ 0 := by
    exact (hω.pos (n + 1)).ne'
  have hratio_coe :
      (((1 : ℝ≥0∞) - (W ω).rightJumpProb (n + 1)) / (W ω).rightJumpProb (n + 1)) =
        ((ratioNN : ℝ≥0) : ℝ≥0∞) := by
    -- Proof comment: this is just the canonical coercion from the NNReal local ratio.
    change (((1 : ℝ≥0) - (W ω).rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞) /
        (W ω).rightJumpProb (n + 1) =
      (((1 : ℝ≥0) - (W ω).rightJumpProb (n + 1)) / (W ω).rightJumpProb (n + 1) : ℝ≥0)
    rw [ENNReal.coe_div hp, ENNReal.coe_sub]
  calc
    (((1 : ℝ≥0∞) - (W ω).rightJumpProb (n + 1)) / (W ω).rightJumpProb (n + 1))
        = ((ratioNN : ℝ≥0) : ℝ≥0∞) := hratio_coe
    _ = ENNReal.ofReal (ratioNN : ℝ) := by
          simp
    _ = ENNReal.ofReal (Real.exp (logρ₊[W](n + 1) ω)) := by
          exact congrArg ENNReal.ofReal hratio_exp

/-- Helper for Exercise 19.6.1: the blocked edge conductances are the boundary conductance
multiplied by the exponential of the negative shifted prefix sums of `logρ₊`. -/
theorem blockedAtZeroEdgeConductance_eq_ofReal_exp_negPrefixSum
    (ω : Ω) (hω : (W ω).IsElliptic) (n : ℕ) :
    blockedAtZeroEdgeConductance (W ω) n =
      ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
        ENNReal.ofReal
          (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
  induction n with
  | zero =>
      -- Proof comment: at the boundary the prefix sum is empty, so the exponential factor is `1`.
      simp [blockedAtZeroEdgeConductance]
  | succ n ih =>
      have hsum :
          Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ₊[W](i + 1) ω) =
            Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω) +
              logρ₊[W](n + 1) ω := by
        simpa using (Finset.sum_range_succ (fun i : ℕ ↦ logρ₊[W](i + 1) ω) n)
      have hexp :
          Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω)) *
              Real.exp (-logρ₊[W](n + 1) ω) =
            Real.exp
              (-Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ₊[W](i + 1) ω)) := by
        rw [← Real.exp_add]
        congr 1
        linarith
      have hinvRatio :
          (ENNReal.ofReal (Real.exp (logρ₊[W](n + 1) ω)))⁻¹ =
            ENNReal.ofReal (Real.exp (-logρ₊[W](n + 1) ω)) := by
        calc
          (ENNReal.ofReal (Real.exp (logρ₊[W](n + 1) ω)))⁻¹
              = ENNReal.ofReal ((Real.exp (logρ₊[W](n + 1) ω))⁻¹) := by
                  rw [ENNReal.ofReal_inv_of_pos (Real.exp_pos _)]
          _ = ENNReal.ofReal (Real.exp (-logρ₊[W](n + 1) ω)) := by
                congr 1
                rw [Real.exp_neg]
      have hmulExp :
          ENNReal.ofReal (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) *
              ENNReal.ofReal (Real.exp (-logρ₊[W](n + 1) ω)) =
            ENNReal.ofReal
              (Real.exp (-Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
        rw [← ENNReal.ofReal_mul (by positivity), hexp]
      -- Proof comment: unfold one recursion step and combine the new inverse ratio into the next
      -- negative exponential factor.
      calc
        blockedAtZeroEdgeConductance (W ω) (n + 1)
            = (ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
                ENNReal.ofReal
                  (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω)))) *
                ENNReal.ofReal (Real.exp (-logρ₊[W](n + 1) ω)) := by
                    rw [blockedAtZeroEdgeConductance_succ, ih,
                      blockedAtZeroLocalRatio_eq_ofReal_exp_logRatio (W := W) ω hω n,
                      div_eq_mul_inv, hinvRatio, mul_assoc]
        _ = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
              ENNReal.ofReal
                (Real.exp (-Finset.sum (Finset.range (n + 1)) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
                  simpa [mul_assoc] using
                    congrArg (fun t ↦ ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) * t) hmulExp

/-- Helper for Exercise 19.6.1: the reciprocal blocked edge conductance is the reciprocal
boundary conductance times the exponential of the shifted prefix sum of `logρ₊`. -/
theorem blockedAtZeroEdgeConductance_inv_eq_ofReal_exp_prefixSum
    (ω : Ω) (hω : (W ω).IsElliptic) (n : ℕ) :
    (blockedAtZeroEdgeConductance (W ω) n)⁻¹ =
      ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)⁻¹) *
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
  have hp0 : 0 < ((W ω).rightJumpProb 0 : ℝ) := by
    exact_mod_cast hω.pos 0
  -- Proof comment: invert the explicit exponential normal form termwise and turn `exp (-s)⁻¹`
  -- back into `exp s`.
  calc
    (blockedAtZeroEdgeConductance (W ω) n)⁻¹
        = (ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
            ENNReal.ofReal
              (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))))⁻¹ := by
              rw [blockedAtZeroEdgeConductance_eq_ofReal_exp_negPrefixSum (W := W) ω hω n]
    _ = ENNReal.ofReal
          ((((W ω).rightJumpProb 0 : ℝ) *
            Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω)))⁻¹) := by
            rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]
    _ = ENNReal.ofReal
          (((W ω).rightJumpProb 0 : ℝ)⁻¹ *
            (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω)))⁻¹) := by
            congr 1
            rw [mul_inv_rev, mul_comm]
    _ = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)⁻¹) *
          ENNReal.ofReal
            ((Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω)))⁻¹) := by
            rw [ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)⁻¹) *
          ENNReal.ofReal
            (Real.exp (Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
            congr 1
            rw [Real.exp_neg, inv_inv]

/-- Helper for Exercise 19.6.1: shifting the half-line log-ratio field by one site preserves the
i.i.d. structure. -/
theorem shiftedLogRatio_isIID (hW : IsHalfLineSolomonEnvironmentLaw μ W) :
    IsIID (fun n ↦ fun ω ↦ logρ₊[W](n + 1) ω) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: the successor map is injective, so the shifted field keeps independence.
    simpa using
      hW.logRatio_iid.iIndepFun.precomp
        (g := Nat.succ) (show Function.Injective Nat.succ from fun _ _ h ↦ Nat.succ.inj h)
  · -- Proof comment: identical distribution is inherited from the ambient half-line Solomon
    -- field after the same shift on both coordinates.
    intro i j
    change IdentDistrib (logρ₊[W](i + 1)) (logρ₊[W](j + 1)) μ μ
    exact hW.identDistrib_logRatio (i + 1) (j + 1)

/-- Helper for Exercise 19.6.1: an eventual strictly negative linear upper bound on the exponent
forces the corresponding exponential ENNReal series to be finite. -/
theorem expSeries_lt_top_of_eventually_linearUpperBound
    {S : ℕ → ℝ} {a : ℝ} (ha : a < 0)
    (hS : Filter.Eventually (fun n : ℕ ↦ S n ≤ a * n) atTop) :
    (∑' n, ENNReal.ofReal (Real.exp (S n))) < ∞ := by
  let r : ℝ := Real.exp a
  have hr_nonneg : 0 ≤ r := by
    -- Proof comment: the geometric comparison ratio is an exponential.
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    -- Proof comment: a negative exponent yields a geometric ratio strictly below `1`.
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr ha
  rcases Filter.eventually_atTop.mp hS with ⟨N, hN⟩
  have hgeom : Summable (fun n : ℕ ↦ r ^ n) := by
    -- Proof comment: once `r ∈ [0, 1)`, the real geometric series is summable.
    simpa [r] using summable_geometric_of_lt_one hr_nonneg hr_lt_one
  have htail :
      Summable (fun k : ℕ ↦ Real.exp (S (k + N))) := by
    have hgeomTail : Summable (fun k : ℕ ↦ r ^ (k + N)) := by
      exact (_root_.summable_nat_add_iff (f := fun n : ℕ ↦ r ^ n) N).2 hgeom
    -- Proof comment: every tail term is bounded by the same-index geometric tail.
    refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) ?_ hgeomTail
    intro k
    have hbound : S (k + N) ≤ a * (k + N : ℕ) := hN (k + N) (Nat.le_add_left N k)
    calc
      Real.exp (S (k + N)) ≤ Real.exp (a * (k + N : ℕ)) := by
        exact Real.exp_le_exp.mpr hbound
      _ = r ^ (k + N) := by
        rw [show a * (k + N : ℕ) = ((k + N : ℕ) : ℝ) * a by ring]
        dsimp [r]
        rw [Real.exp_nat_mul]
  have hsummable : Summable (fun n : ℕ ↦ Real.exp (S n)) := by
    -- Proof comment: summability of one tail is equivalent to summability of the full sequence.
    exact (_root_.summable_nat_add_iff (f := fun n : ℕ ↦ Real.exp (S n)) N).mp htail
  -- Proof comment: a nonnegative summable real series maps to a finite ENNReal series under
  -- `ENNReal.ofReal`.
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) hsummable]
  exact ENNReal.ofReal_lt_top

/-- Helper for Exercise 19.6.1: if the exponent is nonnegative infinitely often, then the
corresponding exponential ENNReal series diverges to `∞`. -/
theorem expSeries_eq_top_of_frequently_nonnegative
    {S : ℕ → ℝ} (hS : ∃ᶠ n in atTop, 0 ≤ S n) :
    (∑' n, ENNReal.ofReal (Real.exp (S n))) = ∞ := by
  let term : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp (S n))
  by_contra hfinite
  have htend : Tendsto term atTop (nhds 0) := by
    -- Proof comment: a finite ENNReal sum forces the summands to tend to `0`.
    exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top (by simpa [term] using hfinite)
  have hhalf_pos : 0 < ENNReal.ofReal (1 / 2 : ℝ) := by
    -- Proof comment: `1 / 2` is a strictly positive contradiction threshold.
    refine ENNReal.ofReal_pos.2 ?_
    norm_num
  have hsmall : ∀ᶠ n in atTop, term n ≤ ENNReal.ofReal (1 / 2 : ℝ) := by
    -- Proof comment: eventual smallness follows from the summands tending to `0`.
    rcases (ENNReal.tendsto_atTop_zero.mp htend) (ENNReal.ofReal (1 / 2 : ℝ)) hhalf_pos with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.mpr ⟨N, hN⟩
  have hhalf_lt_one : ENNReal.ofReal (1 / 2 : ℝ) < ENNReal.ofReal (1 : ℝ) := by
    -- Proof comment: the frequent lower bound `≥ 1` is strictly above the eventual threshold.
    norm_num
  have hlarge : ∃ᶠ n in atTop, ENNReal.ofReal (1 / 2 : ℝ) < term n := by
    -- Proof comment: every nonnegative exponent contributes a term at least `exp 0 = 1`.
    refine hS.mono ?_
    intro n hn
    have hone_le : (1 : ℝ) ≤ Real.exp (S n) := by
      simpa using (Real.exp_le_exp.mpr hn : Real.exp 0 ≤ Real.exp (S n))
    have hone_term : ENNReal.ofReal (1 : ℝ) ≤ term n := by
      exact ENNReal.ofReal_le_ofReal hone_le
    exact lt_of_lt_of_le hhalf_lt_one hone_term
  have hnot_large : ¬ ∃ᶠ n in atTop, ENNReal.ofReal (1 / 2 : ℝ) < term n := by
    -- Proof comment: eventual upper bounds rule out frequent visits above the same threshold.
    rw [Filter.not_frequently]
    exact hsmall.mono fun n hn ↦ not_lt.mpr hn
  exact hnot_large hlarge

/-- Helper for Exercise 19.6.1: if a real sequence does not tend to `-∞`, then its exponential
series cannot have finite ENNReal sum. -/
theorem expSeries_eq_top_of_not_tendsto_atBot
    {S : ℕ → ℝ} (hS : ¬ Tendsto S atTop atBot) :
    (∑' n, ENNReal.ofReal (Real.exp (S n))) = ∞ := by
  let term : ℕ → ℝ≥0∞ := fun n ↦ ENNReal.ofReal (Real.exp (S n))
  rw [tendsto_atTop_atBot] at hS
  push_neg at hS
  rcases hS with ⟨b, hb⟩
  have hlarge : ∃ᶠ n in atTop, ENNReal.ofReal (Real.exp b) ≤ term n := by
    -- Proof comment: failing to converge to `-∞` means one exponential lower bound occurs
    -- infinitely often.
    rw [Filter.frequently_atTop]
    intro N
    rcases hb N with ⟨n, hnN, hbn⟩
    refine ⟨n, hnN, ?_⟩
    exact ENNReal.ofReal_le_ofReal (le_of_lt (Real.exp_lt_exp.mpr hbn))
  by_contra hfinite
  have hfiniteSet :
      {n : ℕ | ENNReal.ofReal (Real.exp b) ≤ term n}.Finite := by
    refine ENNReal.finite_const_le_of_tsum_ne_top ?_ ?_
    · simpa [term] using hfinite
    · exact (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hnot_large : ¬ ∃ᶠ n in atTop, ENNReal.ofReal (Real.exp b) ≤ term n := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hfiniteSet.not_infinite
  exact hnot_large hlarge

/-- Helper for Exercise 19.6.1: along the one-sided shift, the Birkhoff sum of the first
coordinate is the ordinary `Finset.range` prefix sum of the path. -/
theorem birkhoffSumEvalZero_eq_rangeSum
    (z : ℕ → ℝ) (n : ℕ) :
    birkhoffSum Stream'.tail (Function.eval 0) n z =
      Finset.sum (Finset.range n) fun i : ℕ ↦ z i := by
  induction n generalizing z with
  | zero =>
      -- Proof comment: both the Birkhoff sum and the ordinary prefix sum are empty at time `0`.
      simp [birkhoffSum]
  | succ n ih =>
      -- Proof comment: peel off the head term and identify the tail contribution recursively.
      rw [birkhoffSum_succ', ih]
      simp [Stream'.tail, Stream'.get, Finset.sum_range_succ', add_comm]

/-- Helper for Exercise 19.6.1: the path law of an i.i.d. real field is the infinite product of
its one-coordinate marginal. -/
theorem iidRealPathMeasure_eq_infinitePi
    {Y : ℕ → Ω → ℝ} (hY_iid : IsIID Y μ) :
    Measure.map (fun ω n ↦ Y n ω) μ =
      Measure.infinitePi (fun _ : ℕ ↦ Measure.map (Y 0) μ) := by
  have hY_aemeas : ∀ n : ℕ, AEMeasurable (Y n) μ := fun n ↦
    (hY_iid.identDistrib n 0).aemeasurable_fst
  -- Proof comment: compare the joint law of the field with the product of its coordinate laws and
  -- collapse identical marginals to the origin law.
  calc
    Measure.map (fun ω n ↦ Y n ω) μ
        = Measure.infinitePi (fun n : ℕ ↦ Measure.map (Y n) μ) := by
            exact (iIndepFun_iff_map_fun_eq_infinitePi_map₀' hY_aemeas).1 hY_iid.iIndepFun
    _ = Measure.infinitePi (fun _ : ℕ ↦ Measure.map (Y 0) μ) := by
          congr 1
          funext n
          exact (hY_iid.identDistrib n 0).map_eq

/-- Helper for Exercise 19.6.1: negating every coordinate of an i.i.d. real field preserves the
i.i.d. structure. -/
theorem isIID_neg {Y : ℕ → Ω → ℝ} (hY_iid : IsIID Y μ) :
    IsIID (fun n ↦ fun ω ↦ -Y n ω) μ := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: independence survives the same measurable negation on every coordinate.
    simpa using
      hY_iid.iIndepFun.comp (fun _ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
  · -- Proof comment: identical distribution is likewise stable under coordinatewise negation.
    intro i j
    simpa using (hY_iid.identDistrib i j).comp measurable_neg

/-- Helper for Exercise 19.6.1: the canonical path law of an i.i.d. real field is ergodic for the
one-sided shift. -/
theorem iidRealPathMeasureErgodic
    {Y : ℕ → Ω → ℝ} (hY_iid : IsIID Y μ) :
    Ergodic Stream'.tail (Measure.map (fun ω n ↦ Y n ω) μ) := by
  let ν : Measure ℝ := Measure.map (Y 0) μ
  have hY0_aemeas : AEMeasurable (Y 0) μ := (hY_iid.identDistrib 0 0).aemeasurable_fst
  letI : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    dsimp [ν]
    rw [Measure.map_apply_of_aemeasurable hY0_aemeas MeasurableSet.univ, Set.preimage_univ]
    simp
  let P : Measure (Stream' ℝ) := Measure.infinitePi (fun _ : ℕ ↦ ν)
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ ν))
    infer_instance
  have hmixing :
      MeasurePreserving Stream'.tail
          P
          P ∧
        IsStronglyMixing Stream'.tail P := by
    -- Proof comment: the one-sided Bernoulli shift is strongly mixing for every product law.
    simpa [ν] using
      (iid_oneSided_product_shift_is_mixing (E := ℝ) ν)
  rcases hmixing with ⟨hpres, hstrong⟩
  have hergodic :
      Ergodic Stream'.tail P :=
    ergodic_of_isStronglyMixing (P := P) hpres hstrong
  -- Proof comment: identify the i.i.d. path law with its Bernoulli product law and transport the
  -- ergodicity statement across that equality.
  have hpath : Measure.map (fun ω n ↦ Y n ω) μ = P := by
    simpa [P, ν] using iidRealPathMeasure_eq_infinitePi (μ := μ) (Y := Y) hY_iid
  exact hpath ▸ hergodic

/-- Helper for Exercise 19.6.1: the `k`-th barrier event asks every positive-time path-space
partial sum to stay above `(1 : ℝ) / (k + 1)`. -/
private def partialSumBarrierEvent (k : ℕ) : Set (ℕ → ℝ) :=
  {ω | ∀ n : ℕ, (1 : ℝ) / (k + 1) < birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω}

/-- Helper for Exercise 19.6.1: the barrier event is measurable because it is a countable
intersection of measurable strict half-spaces for the positive-time partial sums. -/
private lemma measurableSet_partialSumBarrierEvent (k : ℕ) :
    MeasurableSet (partialSumBarrierEvent k) := by
  -- Proof comment: rewrite the barrier condition as one inequality for each positive time and
  -- intersect those measurable slices.
  suffices
      MeasurableSet
        (⋂ n : ℕ,
          {ω : ℕ → ℝ | (1 : ℝ) / (k + 1) <
            birkhoffSum Stream'.tail (Function.eval 0) (n + 1) ω}) by
    simpa [partialSumBarrierEvent, Set.setOf_forall]
  refine MeasurableSet.iInter fun n : ℕ ↦ ?_
  exact measurableSet_lt measurable_const (measurablePartialSumEvalZero (n + 1))

/-- Helper for Exercise 19.6.1: the barrier-event definition matches the source-style
formulation `∀ m ≥ 1, ε < S_m`. -/
private lemma mem_partialSumBarrierEvent_iff {k : ℕ} {ω : ℕ → ℝ} :
    ω ∈ partialSumBarrierEvent k ↔
      ∀ m ≥ 1, (1 : ℝ) / (k + 1) < birkhoffSum Stream'.tail (Function.eval 0) m ω := by
  constructor
  · intro h m hm
    rcases Nat.exists_eq_add_of_le hm with ⟨n, rfl⟩
    simpa [Nat.add_assoc, Nat.add_comm] using h n
  · intro h n
    simpa using h (n + 1) (Nat.succ_le_succ (Nat.zero_le n))

/-- Helper for Exercise 19.6.1: shifting by `j` subtracts the initial `j`-term partial sum from
the later path-space partial sums. -/
private lemma partialSum_iterate_tail_eq_sub (j m : ℕ) (ω : ℕ → ℝ) :
    birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) =
      birkhoffSum Stream'.tail (Function.eval 0) (j + m) ω -
        birkhoffSum Stream'.tail (Function.eval 0) j ω := by
  -- Proof comment: split the long Birkhoff sum at time `j` and then move the initial block to
  -- the other side of the equality.
  have hsplit :
      birkhoffSum Stream'.tail (Function.eval 0) (j + m) ω =
        birkhoffSum Stream'.tail (Function.eval 0) j ω +
          birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) :=
    birkhoffSum_add Stream'.tail (Function.eval 0) j m ω
  have hsub :=
    congrArg
      (fun t : ℝ ↦ t - birkhoffSum Stream'.tail (Function.eval 0) j ω)
      hsplit
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hsub.symm

/-- Helper for Exercise 19.6.1: the barrier-event indicator is integrable on any probability path
space. -/
private lemma integrable_partialSumBarrierIndicator
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (k : ℕ) :
    Integrable ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) P := by
  -- Proof comment: on a probability space the indicator is bounded by the integrable constant
  -- `1`.
  exact (integrable_const (1 : ℝ)).indicator (measurableSet_partialSumBarrierEvent k)

/-- Helper for Exercise 19.6.1: among the first `N + 1` partial sums, there is a last index where
the prefix minimum is attained. -/
private lemma existsLastPrefixMinimum (S : ℕ → ℝ) (N : ℕ) :
    ∃ j ≤ N, (∀ i ≤ N, S j ≤ S i) ∧ ∀ ⦃i : ℕ⦄, j < i → i ≤ N → S j < S i := by
  classical
  -- Route correction: choose the maximal index among all minimizers of the finite prefix so the
  -- required strict inequality at later prefix indices is built into the witness.
  let p : ℕ → Prop := fun j ↦ ∀ i ∈ Finset.range (N + 1), S j ≤ S i
  letI : DecidablePred p := Classical.decPred p
  let minimizers : Finset ℕ :=
    (Finset.range (N + 1)).filter p
  have hminimizers_ne : minimizers.Nonempty := by
    obtain ⟨j, hj_mem, hj_min⟩ :=
      Finset.exists_min_image (Finset.range (N + 1)) S ⟨0, by simp⟩
    refine ⟨j, ?_⟩
    refine Finset.mem_filter.mpr ⟨hj_mem, ?_⟩
    intro i hi
    exact hj_min i hi
  let j : ℕ := minimizers.max' hminimizers_ne
  have hj_mem : j ∈ minimizers := Finset.max'_mem minimizers hminimizers_ne
  have hj_prop : ∀ i ∈ Finset.range (N + 1), S j ≤ S i := (Finset.mem_filter.mp hj_mem).2
  have hjN : j ≤ N := by
    exact Nat.lt_succ_iff.mp (by simpa [minimizers, p] using (Finset.mem_filter.mp hj_mem).1)
  refine ⟨j, hjN, ?_⟩
  constructor
  · intro i hiN
    exact hj_prop i (by simpa using Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiN))
  · intro i hji hiN
    have hle : S j ≤ S i := by
      exact hj_prop i (by simpa using Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiN))
    by_cases hEq : S j = S i
    · have hi_prefix : i ∈ Finset.range (N + 1) := by
        simpa using Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hiN)
      have hi_mem : i ∈ minimizers := by
        refine Finset.mem_filter.mpr ⟨hi_prefix, ?_⟩
        intro m hm
        calc
          S i = S j := hEq.symm
          _ ≤ S m := hj_prop m hm
      have hi_le_j : i ≤ j := Finset.le_max' minimizers i hi_mem
      exact (not_le_of_gt hji hi_le_j).elim
    · exact lt_of_le_of_ne hle hEq

/-- Helper for Exercise 19.6.1: the last prefix minimum and an eventually positive tail produce a
rational barrier event after the corresponding shift. -/
private lemma lastPrefixMinimumHasBarrierIndex {ω : ℕ → ℝ} {N j : ℕ}
    (_hjN : j ≤ N)
    (hmin :
      ∀ i ≤ N,
        birkhoffSum Stream'.tail (Function.eval 0) j ω ≤
          birkhoffSum Stream'.tail (Function.eval 0) i ω)
    (hstrict :
      ∀ ⦃i : ℕ⦄,
        j < i → i ≤ N →
          birkhoffSum Stream'.tail (Function.eval 0) j ω <
            birkhoffSum Stream'.tail (Function.eval 0) i ω)
    (hTail :
      ∀ n ≥ N,
        1 ≤ birkhoffSum Stream'.tail (Function.eval 0) n ω) :
    ∃ k : ℕ, Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
  let S : ℕ → ℝ := fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω
  have hS0 : S 0 = 0 := by
    simp [S, birkhoffSum]
  have hSj_nonpos : S j ≤ 0 := by
    have hj0 : S j ≤ S 0 := hmin 0 (Nat.zero_le N)
    simpa [hS0] using hj0
  by_cases hExists : ∃ i : ℕ, j < i ∧ i ≤ N
  · classical
    -- Route correction: isolate the finite positive gaps above the last minimum and choose the
    -- barrier from their minimum before rewriting shifted partial sums.
    obtain ⟨i₀, hj_i₀, hi₀N⟩ := hExists
    let active : Finset ℕ := Finset.Icc (j + 1) N
    have hactive_ne : active.Nonempty := by
      refine ⟨i₀, ?_⟩
      simp [active, Nat.succ_le_of_lt hj_i₀, hi₀N]
    obtain ⟨iMin, hiMin_mem, hiMin_min⟩ :=
      Finset.exists_min_image active (fun i ↦ S i - S j) hactive_ne
    have hiMin_gt : j < iMin := by
      exact lt_of_lt_of_le (Nat.lt_succ_self j) (Finset.mem_Icc.mp hiMin_mem).1
    have hiMinN : iMin ≤ N := (Finset.mem_Icc.mp hiMin_mem).2
    have hgap_pos : 0 < S iMin - S j := by
      have hstrict_pos : S j < S iMin := hstrict hiMin_gt hiMinN
      linarith
    let δ : ℝ := min 1 (S iMin - S j)
    have hδpos : 0 < δ := by
      dsimp [δ]
      positivity
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hδpos
    refine ⟨k, (mem_partialSumBarrierEvent_iff).2 ?_⟩
    intro m hm
    have hm_pos : 0 < m := Nat.succ_le_iff.mp hm
    have hshift :
        birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) =
          S (j + m) - S j := by
      simpa [S] using partialSum_iterate_tail_eq_sub j m ω
    by_cases hmN : j + m ≤ N
    · -- Proof comment: inside the finite prefix, the chosen gap minimum controls all shifted sums.
      have hjm_mem : j + m ∈ active := by
        simp [active, hmN, Nat.succ_le_iff.mpr hm_pos]
      have hgap_lower : S iMin - S j ≤ S (j + m) - S j := hiMin_min (j + m) hjm_mem
      have hδ_le_gap : δ ≤ S (j + m) - S j := by
        exact le_trans (min_le_right 1 (S iMin - S j)) hgap_lower
      rw [hshift]
      exact lt_of_lt_of_le hk hδ_le_gap
    · -- Proof comment: once the time lies past `N`, eventual positivity and `S j ≤ 0` give a
      -- uniform lower bound by `1`.
      have htail : 1 ≤ S (j + m) := hTail (j + m) (le_of_not_ge hmN)
      have hgap_one : 1 ≤ S (j + m) - S j := by
        linarith
      have hδ_le_one : δ ≤ 1 := min_le_left 1 (S iMin - S j)
      rw [hshift]
      exact lt_of_lt_of_le hk (le_trans hδ_le_one hgap_one)
  · -- Proof comment: if there is no later prefix index, then `j = N`, so every positive-time
    -- shifted sum is already in the eventual tail and stays above the fixed barrier `1/2`.
    refine ⟨1, (mem_partialSumBarrierEvent_iff).2 ?_⟩
    intro m hm
    have hm_pos : 0 < m := Nat.succ_le_iff.mp hm
    have hm_tail : ¬ j + m ≤ N := by
      intro hmN
      exact hExists ⟨j + m, by omega, hmN⟩
    have hshift :
        birkhoffSum Stream'.tail (Function.eval 0) m (Stream'.tail^[j] ω) =
          S (j + m) - S j := by
      simpa [S] using partialSum_iterate_tail_eq_sub j m ω
    have htail : 1 ≤ S (j + m) := hTail (j + m) (le_of_not_ge hm_tail)
    have hgap_one : 1 ≤ S (j + m) - S j := by
      linarith
    rw [hshift]
    have hhalf : (1 : ℝ) / ((1 : ℕ) + 1) < 1 := by
      norm_num
    exact lt_of_lt_of_le hhalf hgap_one

/-- Helper for Exercise 19.6.1: along a path whose partial sums tend to `+∞`, some shift of the
path enters a rational barrier event. -/
private lemma existsShiftPositiveBarrierOfPartialSumAtTop {ω : ℕ → ℝ}
    (hω :
      Tendsto
        (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
        atTop atTop) :
    ∃ j k : ℕ, Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
  let S : ℕ → ℝ := fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω
  have hEventually : ∀ᶠ n in atTop, 1 ≤ S n := by
    simpa [S] using (tendsto_atTop.1 hω) (1 : ℝ)
  rcases Filter.mem_atTop_sets.mp hEventually with ⟨N, hN⟩
  obtain ⟨j, hjN, hmin, hstrict⟩ := existsLastPrefixMinimum S N
  have hTail : ∀ n ≥ N, 1 ≤ S n := by
    intro n hn
    exact hN n hn
  rcases lastPrefixMinimumHasBarrierIndex (ω := ω) hjN
      (by simpa [S] using hmin)
      (by simpa [S] using hstrict)
      (by simpa [S] using hTail) with ⟨k, hk⟩
  exact ⟨j, k, hk⟩

/-- Helper for Exercise 19.6.1: almost-sure divergence of the path-space partial sums yields a
barrier event of strictly positive probability. -/
private lemma exists_posMeasure_positiveBarrierEvent
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (hP : Ergodic Stream'.tail P)
    (hAe :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
          atTop atTop) :
    ∃ k : ℕ, 0 < P (partialSumBarrierEvent k) := by
  let A : Set (ℕ → ℝ) := {ω |
    Tendsto
      (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
      atTop atTop}
  let E : ℕ × ℕ → Set (ℕ → ℝ) := fun p ↦ (Stream'.tail^[p.1]) ⁻¹' partialSumBarrierEvent p.2
  have hcover : A ⊆ ⋃ p : ℕ × ℕ, E p := by
    intro ω hω
    rcases existsShiftPositiveBarrierOfPartialSumAtTop hω with ⟨j, k, hjk⟩
    refine Set.mem_iUnion.mpr ⟨(j, k), ?_⟩
    simpa [E]
  have hAae : A =ᵐ[P] Set.univ := by
    simpa [A] using hAe
  have hAone : P A = 1 := by
    simpa using measure_congr hAae
  have hUnionPos : 0 < P (⋃ p : ℕ × ℕ, E p) := by
    calc
      0 < P A := by simp [hAone]
      _ ≤ P (⋃ p : ℕ × ℕ, E p) := measure_mono hcover
  obtain ⟨p, hp⟩ :
      ∃ p : ℕ × ℕ, 0 < P (E p) :=
    MeasureTheory.exists_measure_pos_of_not_measure_iUnion_null (ne_of_gt hUnionPos)
  refine ⟨p.2, ?_⟩
  have hpreimage :
      P (E p) = P (partialSumBarrierEvent p.2) := by
    simpa [E] using
      (hP.toMeasurePreserving.iterate p.1).measure_preimage
        (measurableSet_partialSumBarrierEvent p.2).nullMeasurableSet
  rwa [hpreimage] at hp

/-- Helper for Exercise 19.6.1: the barrier visits before time `n` are the indices `i < n` whose
shifted path lies in the `k`-th barrier event. -/
private noncomputable def partialSumBarrierVisitTimes (k n : ℕ) (ω : ℕ → ℝ) : Finset ℕ :=
  @Finset.filter ℕ (fun i => Stream'.tail^[i] ω ∈ partialSumBarrierEvent k)
    (Classical.decPred _) (Finset.range n)

/-- Helper for Exercise 19.6.1: the Birkhoff sum of the barrier indicator counts barrier
visits. -/
private lemma birkhoffSum_partialSumBarrierIndicator_eq_card (k n : ℕ) (ω : ℕ → ℝ) :
    birkhoffSum Stream'.tail ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) n ω =
      (partialSumBarrierVisitTimes k n ω).card := by
  classical
  -- Proof comment: unfold the Birkhoff sum into a finite `0`/`1` sum and identify it with the
  -- filtered range cardinality of barrier-visit times.
  rw [birkhoffSum]
  simp only [Set.indicator_apply]
  rw [Finset.sum_boole]
  rfl

/-- Helper for Exercise 19.6.1: every barrier visit contributes one more uniform barrier
increment to every later partial sum. -/
private lemma partialSumLowerBoundOfPositiveBarrierVisits {ω : ℕ → ℝ} {L : ℝ} {k n : ℕ}
    (hL :
      ∀ m : ℕ,
        L ≤ birkhoffSum Stream'.tail (Function.eval 0) m ω) :
    L + (1 : ℝ) / (k + 1) * (partialSumBarrierVisitTimes k n ω).card ≤
      birkhoffSum Stream'.tail (Function.eval 0) n ω := by
  classical
  let ε : ℝ := (1 : ℝ) / (k + 1)
  let S : ℕ → ℝ := fun m ↦ birkhoffSum Stream'.tail (Function.eval 0) m ω
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  -- Route correction: recurse on the maximal barrier visit before `n`, so the counting step is
  -- a single card decomposition plus one barrier increment.
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hVisits : (partialSumBarrierVisitTimes k n ω).Nonempty
      · let visits : Finset ℕ := partialSumBarrierVisitTimes k n ω
        let i : ℕ := visits.max' hVisits
        have hi_mem : i ∈ visits := Finset.max'_mem visits hVisits
        have hi_props : i < n ∧ Stream'.tail^[i] ω ∈ partialSumBarrierEvent k := by
          simpa [visits, partialSumBarrierVisitTimes] using hi_mem
        have hi_lt_n : i < n := hi_props.1
        have hi_barrier : Stream'.tail^[i] ω ∈ partialSumBarrierEvent k := hi_props.2
        have hprev_eq : partialSumBarrierVisitTimes k i ω = visits.erase i := by
          ext j
          constructor
          · intro hj
            have hj_props : j < i ∧ Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
              simpa [partialSumBarrierVisitTimes] using hj
            have hj_lt_n : j < n := lt_trans hj_props.1 hi_lt_n
            have hj_ne : j ≠ i := Nat.ne_of_lt hj_props.1
            simp [visits, partialSumBarrierVisitTimes, hj_lt_n, hj_props.2, hj_ne]
          · intro hj
            rcases Finset.mem_erase.mp hj with ⟨hj_ne, hj_mem_visits⟩
            have hj_props : j < n ∧ Stream'.tail^[j] ω ∈ partialSumBarrierEvent k := by
              simpa [visits, partialSumBarrierVisitTimes] using hj_mem_visits
            have hj_le_i : j ≤ i := Finset.le_max' visits j hj_mem_visits
            have hj_lt_i : j < i := lt_of_le_of_ne hj_le_i hj_ne
            simp [partialSumBarrierVisitTimes, hj_lt_i, hj_props.2]
        have hcard_nat :
            (partialSumBarrierVisitTimes k n ω).card =
              (partialSumBarrierVisitTimes k i ω).card + 1 := by
          calc
            visits.card = (visits.erase i).card + 1 := (Finset.card_erase_add_one hi_mem).symm
            _ = (partialSumBarrierVisitTimes k i ω).card + 1 := by rw [← hprev_eq]
        have hcard_real :
            ((partialSumBarrierVisitTimes k n ω).card : ℝ) =
              ((partialSumBarrierVisitTimes k i ω).card : ℝ) + 1 := by
          rw [hcard_nat, Nat.cast_add, Nat.cast_one]
        have hih :
            L + ε * (partialSumBarrierVisitTimes k i ω).card ≤ S i := by
          simpa [S, ε] using ih i hi_lt_n
        have hi_barrier' := (mem_partialSumBarrierEvent_iff).1 hi_barrier
        have hni : 1 ≤ n - i := by
          omega
        have hgap_shift :
            ε <
              birkhoffSum Stream'.tail (Function.eval 0) (n - i) (Stream'.tail^[i] ω) := by
          simpa [ε] using hi_barrier' (n - i) hni
        have hshift :
            birkhoffSum Stream'.tail (Function.eval 0) (n - i) (Stream'.tail^[i] ω) =
              S n - S i := by
          simpa [S, Nat.add_sub_of_le hi_lt_n.le] using partialSum_iterate_tail_eq_sub i (n - i) ω
        have hgap : ε < S n - S i := by
          rw [← hshift]
          exact hgap_shift
        rw [hcard_real]
        have hstep :
            L + ε * (((partialSumBarrierVisitTimes k i ω).card : ℝ) + 1) < S n := by
          calc
            L + ε * (((partialSumBarrierVisitTimes k i ω).card : ℝ) + 1)
                = (L + ε * (partialSumBarrierVisitTimes k i ω).card) + ε := by ring
            _ ≤ S i + ε := by gcongr
            _ < S n := by linarith
        exact le_of_lt hstep
      · have hEmpty : partialSumBarrierVisitTimes k n ω = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hVisits
        -- Proof comment: if there is no barrier visit before `n`, the estimate reduces to the
        -- global lower bound `L ≤ S n`.
        rw [hEmpty, Finset.card_empty, Nat.cast_zero, mul_zero, add_zero]
        simpa [S] using hL n

/-- Helper for Exercise 19.6.1: dividing the visit-count inequality by `n + 1` turns it into a
comparison between the barrier-indicator average and the original partial-sum average. -/
private lemma scaledBarrierVisitAverage_le_partialSumAverage {ω : ℕ → ℝ} {L : ℝ} {k n : ℕ}
    (hL :
      ∀ m : ℕ,
        L ≤ birkhoffSum Stream'.tail (Function.eval 0) m ω) :
    (((n + 1 : ℕ) : ℝ)⁻¹ * L) +
        (1 : ℝ) / (k + 1) *
          birkhoffAverage ℝ Stream'.tail
            ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) (n + 1) ω ≤
      birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω := by
  let m : ℕ := n + 1
  let ε : ℝ := (1 : ℝ) / (k + 1)
  have hscaled :
      (m : ℝ)⁻¹ *
          (L + ε * (partialSumBarrierVisitTimes k m ω).card) ≤
        (m : ℝ)⁻¹ * birkhoffSum Stream'.tail (Function.eval 0) m ω := by
    have hcount :=
      partialSumLowerBoundOfPositiveBarrierVisits
        (ω := ω) (L := L) (k := k) (n := m) hL
    exact mul_le_mul_of_nonneg_left hcount (by positivity)
  -- Proof comment: rewrite both sides into `birkhoffAverage` normal form only once.
  have hleft :
      (m : ℝ)⁻¹ * (L + ε * (partialSumBarrierVisitTimes k m ω).card) =
        ((m : ℝ)⁻¹ * L) +
          ε *
            birkhoffAverage ℝ Stream'.tail
              ((partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))) m ω := by
    rw [birkhoffAverage, smul_eq_mul, birkhoffSum_partialSumBarrierIndicator_eq_card]
    ring
  have hright :
      (m : ℝ)⁻¹ * birkhoffSum Stream'.tail (Function.eval 0) m ω =
        birkhoffAverage ℝ Stream'.tail (Function.eval 0) m ω := by
    rw [birkhoffAverage, smul_eq_mul]
  rw [hleft, hright] at hscaled
  simpa [m, ε] using hscaled

/-- Helper for Exercise 19.6.1: almost-sure divergence of the path-space partial sums forces a
strictly positive expectation of the first-coordinate observable. -/
private lemma expectation_pos_of_partialSumAtTop_ae
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (hP : Ergodic Stream'.tail P)
    (h_int : Integrable (Function.eval 0) P)
    (hAe :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω)
          atTop atTop) :
    0 < P[Function.eval 0] := by
  obtain ⟨k, hkPos⟩ := exists_posMeasure_positiveBarrierEvent P hP hAe
  let ε : ℝ := (1 : ℝ) / (k + 1)
  let g : (ℕ → ℝ) → ℝ := (partialSumBarrierEvent k).indicator (fun _ : ℕ → ℝ ↦ (1 : ℝ))
  have hg_int : Integrable g P := by
    simpa [g] using integrable_partialSumBarrierIndicator P k
  have hAverageEval :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) n ω)
          atTop
          (nhds (P[Function.eval 0])) :=
    birkhoffAverage_tendsto_ae_expectation_of_ergodic
      (P := P) (τ := Stream'.tail) (f := Function.eval 0) hP h_int
  have hAverageBarrier :
      ∀ᵐ ω ∂P,
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail g n ω)
          atTop
          (nhds (P[g])) :=
    birkhoffAverage_tendsto_ae_expectation_of_ergodic
      (P := P) (τ := Stream'.tail) (f := g) hP hg_int
  have hgExpectation : P[g] = P.real (partialSumBarrierEvent k) := by
    -- Proof comment: the expectation of the barrier indicator is the real-valued probability of
    -- the barrier event.
    simpa [g] using
      (integral_indicator_one (μ := P) (s := partialSumBarrierEvent k)
        (measurableSet_partialSumBarrierEvent k))
  have hgPos : 0 < P[g] := by
    rw [hgExpectation]
    exact ENNReal.toReal_pos (ne_of_gt hkPos) (measure_ne_top P _)
  have hLowerAe : ∀ᵐ ω ∂P, ε * P[g] ≤ P[Function.eval 0] := by
    filter_upwards [hAe, hAverageEval, hAverageBarrier] with ω hDiv hEval hBarrier
    let S : ℕ → ℝ := fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n ω
    have hEventuallyNonneg : ∀ᶠ n in atTop, 0 ≤ S n := by
      simpa [S] using (tendsto_atTop.1 hDiv) (0 : ℝ)
    rcases Filter.mem_atTop_sets.mp hEventuallyNonneg with ⟨N, hN⟩
    obtain ⟨j, hjmem, hjmin⟩ := Finset.exists_min_image (Finset.range (N + 1)) S
      ⟨0, by simp⟩
    have hLower :
        ∀ m : ℕ, S j ≤ S m := by
      intro m
      by_cases hm : m ≤ N
      · exact hjmin m <| by simp [hm]
      · have hj0 : S j ≤ S 0 := hjmin 0 <| by simp
        have hmNonneg : 0 ≤ S m := hN m (Nat.le_of_lt (Nat.lt_of_not_ge hm))
        have hjNonpos : S j ≤ 0 := by simpa [S] using hj0
        linarith
    have hBarrierShift :
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail g (n + 1) ω)
          atTop
          (nhds (P[g])) :=
      (tendsto_add_atTop_iff_nat 1).2 hBarrier
    have hDecay :
        Tendsto
          (fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹ * S j))
          atTop
          (nhds (0 : ℝ)) := by
      have hInv :
          Tendsto
            (fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹))
            atTop
            (nhds (0 : ℝ)) := by
        exact (((tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop)).inv_tendsto_atTop
      simpa using hInv.mul tendsto_const_nhds
    have hScaledBarrier :
        Tendsto
          (fun n ↦ ε * birkhoffAverage ℝ Stream'.tail g (n + 1) ω)
          atTop
          (nhds (ε * P[g])) := by
      simpa [ε] using tendsto_const_nhds.mul hBarrierShift
    have hEvalShift :
        Tendsto
          (fun n ↦ birkhoffAverage ℝ Stream'.tail (Function.eval 0) (n + 1) ω)
          atTop
          (nhds (P[Function.eval 0])) :=
      (tendsto_add_atTop_iff_nat 1).2 hEval
    have hLeft :
        Tendsto
          (fun n ↦ (((n + 1 : ℕ) : ℝ)⁻¹ * S j) +
            ε * birkhoffAverage ℝ Stream'.tail g (n + 1) ω)
          atTop
          (nhds (ε * P[g])) := by
      simpa using hDecay.add hScaledBarrier
    -- Proof comment: compare the two convergent shifted averages through the pointwise lower
    -- bound supplied by the barrier-visit estimate.
    exact le_of_tendsto_of_tendsto' hLeft hEvalShift fun n ↦
      scaledBarrierVisitAverage_le_partialSumAverage
        (ω := ω) (L := S j) (k := k) (n := n) (by simpa [S] using hLower)
  have hBound : ε * P[g] ≤ P[Function.eval 0] := by
    by_contra hlt
    have hFalse : ∀ᵐ ω ∂P, False := hLowerAe.mono fun _ hω ↦ hlt hω
    have hUnivZero : P Set.univ = 0 := by
      simp [ae_iff] at hFalse
    have hUnivOne : P Set.univ = 1 := by
      simp
    rw [hUnivZero] at hUnivOne
    norm_num at hUnivOne
  have hPos : 0 < ε * P[g] := by
    have hεpos : 0 < ε := by
      dsimp [ε]
      positivity
    nlinarith
  exact lt_of_lt_of_le hPos hBound

/-- Helper for Exercise 19.6.1: a zero-mean i.i.d. real field has prefix sums that almost surely
do not tend to `-∞`. -/
theorem ae_not_tendsto_atBot_prefixSum_of_mean_zero
    {Y : ℕ → Ω → ℝ}
    (hint : Integrable (Y 0) μ)
    (hY_iid : IsIID Y μ)
    (hmean : ∫ ω, Y 0 ω ∂μ = 0) :
    ∀ᵐ ω ∂μ,
      ¬ Tendsto
        (fun n ↦ Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω))
        atTop atBot := by
  -- Route correction: port the owner barrier-event path-space API locally, then pull the
  -- contradiction back along the negated path map.
  let Z : ℕ → Ω → ℝ := fun n ω ↦ -Y n ω
  let pathZ : Ω → ℕ → ℝ := fun ω n ↦ Z n ω
  let P : Measure (ℕ → ℝ) := Measure.map pathZ μ
  have hpathZ_aemeas : AEMeasurable pathZ μ := by
    -- Proof comment: each coordinate is a.e. measurable, so the path map is a.e. measurable in
    -- the product sigma-algebra.
    refine aemeasurable_pi_lambda _ fun n ↦ ?_
    exact ((isIID_neg (μ := μ) hY_iid).identDistrib n 0).aemeasurable_fst
  letI : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    dsimp [P]
    rw [Measure.map_apply_of_aemeasurable hpathZ_aemeas MeasurableSet.univ, Set.preimage_univ]
    simp
  let B : Set (ℕ → ℝ) := {z |
    Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n z) atTop atTop}
  have hZ_iid : IsIID Z μ := isIID_neg (μ := μ) hY_iid
  have hP_ergodic : Ergodic Stream'.tail P := by
    -- Proof comment: the i.i.d. path law is ergodic for the one-sided shift.
    simpa [P, pathZ, Z] using iidRealPathMeasureErgodic (μ := μ) (Y := Z) hZ_iid
  have hP_int : Integrable (Function.eval 0) P := by
    -- Proof comment: the first coordinate under the path law is exactly the negated origin
    -- variable.
    rw [show P = Measure.map pathZ μ by rfl]
    refine
      (integrable_map_measure
        (μ := μ) (f := pathZ) (g := Function.eval 0)
        (measurable_pi_apply 0).aestronglyMeasurable hpathZ_aemeas).2 ?_
    change Integrable (fun ω ↦ -Y 0 ω) μ
    simpa using hint.neg
  have hP_meanZero : P[Function.eval 0] = 0 := by
    -- Proof comment: transport the zero mean of `Y 0` through the negated path map.
    change ∫ z, Function.eval 0 z ∂P = 0
    rw [show P = Measure.map pathZ μ by rfl,
      integral_map hpathZ_aemeas (measurable_pi_apply 0).aestronglyMeasurable]
    simpa [pathZ, Z, integral_neg, hmean]
  have hB_meas : MeasurableSet B := by
    -- Proof comment: the path-space `atTop` event is measurable because each Birkhoff sum is.
    exact measurableSet_tendsto atTop measurablePartialSumEvalZero
  have hB_zero : P B = 0 := by
    by_contra hB_ne_zero
    have hB_pos : 0 < P B := bot_lt_iff_ne_bot.mpr hB_ne_zero
    have hB_ae :
        ∀ᵐ z ∂P,
          Tendsto (fun n ↦ birkhoffSum Stream'.tail (Function.eval 0) n z) atTop atTop :=
      (orbit_partial_sum_tendsto_atTop_ae_iff_measure_pos_of_ergodic
        P hP_ergodic (measurable_pi_apply 0)).2 hB_pos
    have hExpPos :
        0 < P[Function.eval 0] :=
      expectation_pos_of_partialSumAtTop_ae P hP_ergodic hP_int hB_ae
    have : 0 < (0 : ℝ) := by
      simpa [hP_meanZero] using hExpPos
    exact lt_irrefl 0 this
  have hpre_ae : pathZ ⁻¹' Bᶜ ∈ ae μ := by
    -- Proof comment: pull the almost-sure exclusion of the bad path event back to the original
    -- probability space.
    have hB_ae_notMem : Bᶜ ∈ ae P := by
      simpa [mem_ae_iff] using hB_zero
    exact (mem_ae_map_iff hpathZ_aemeas hB_meas.compl).mp hB_ae_notMem
  filter_upwards [hpre_ae] with ω hω
  intro hbad
  -- Proof comment: if the prefix sums tended to `-∞`, then the negated path would land in the
  -- forbidden shift-ergodic event.
  have hpathBad : pathZ ω ∈ B := by
    have hneg :
        Tendsto
          (fun n : ℕ ↦ -(Finset.sum (Finset.range n) (fun i : ℕ ↦ Y i ω)))
          atTop atTop :=
      tendsto_neg_atTop_iff.2 hbad
    simpa [B, pathZ, Z, birkhoffSumEvalZero_eq_rangeSum, Finset.sum_neg_distrib] using hneg
  have hnotBad : pathZ ω ∉ B := by
    simpa [Set.preimage, Set.mem_compl_iff] using hω
  exact hnotBad hpathBad

/-- Helper for Exercise 19.6.1: negative mean makes the reciprocal blocked edge-conductance
series summable almost surely. -/
theorem ae_blockedAtZeroResistanceSeries_lt_top_of_integral_logRatio_lt_zero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ, (∑' n, (blockedAtZeroEdgeConductance (W ω) n)⁻¹) < ∞ := by
  have hshiftMean : ∫ ω, logρ₊[W](1) ω ∂μ < 0 := by
    rw [show ∫ ω, logρ₊[W](1) ω ∂μ = ∫ ω, logρ₊[W](0) ω ∂μ by
      simpa using (IsHalfLineSolomonEnvironmentLaw.identDistrib_logRatio hW 1 0).integral_eq]
    exact hmean
  have hprefix :=
    ae_eventually_prefixSum_le_halfMean_mul_of_mean_neg
      (μ := μ) (Y := fun n ↦ fun ω ↦ logρ₊[W](n + 1) ω)
      (IsHalfLineSolomonEnvironmentLaw.integrable_logRatio hW hlog 1)
      (shiftedLogRatio_isIID (μ := μ) (W := W) hW) hshiftMean
  have hcoeff : (∫ ω, logρ₊[W](1) ω ∂μ) / 2 < 0 := by
    linarith
  filter_upwards [hW.ae_elliptic, hprefix] with ω hω hω_prefix
  have hseries :
      (∑' n : ℕ,
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ₊[W](i + 1) ω))) < ∞ :=
    expSeries_lt_top_of_eventually_linearUpperBound hcoeff hω_prefix
  have hterms :
      (fun n : ℕ ↦ (blockedAtZeroEdgeConductance (W ω) n)⁻¹) =
        fun n : ℕ ↦
          ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)⁻¹) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ₊[W](i + 1) ω)) := by
    funext n
    simpa using blockedAtZeroEdgeConductance_inv_eq_ofReal_exp_prefixSum (W := W) ω hω n
  rw [hterms, ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hseries

/-- Helper for Exercise 19.6.1: at zero mean the reciprocal blocked edge-conductance series
diverges almost surely. -/
theorem ae_blockedAtZeroResistanceSeries_eq_top_of_integral_logRatio_eq_zero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, (∑' n, (blockedAtZeroEdgeConductance (W ω) n)⁻¹) = ∞ := by
  have hshiftMean : ∫ ω, logρ₊[W](1) ω ∂μ = 0 := by
    rw [show ∫ ω, logρ₊[W](1) ω ∂μ = ∫ ω, logρ₊[W](0) ω ∂μ by
      simpa using (IsHalfLineSolomonEnvironmentLaw.identDistrib_logRatio hW 1 0).integral_eq]
    exact hmean
  have hprefix :=
    ae_not_tendsto_atBot_prefixSum_of_mean_zero
      (μ := μ) (Y := fun n ↦ fun ω ↦ logρ₊[W](n + 1) ω)
      (IsHalfLineSolomonEnvironmentLaw.integrable_logRatio hW hlog 1)
      (shiftedLogRatio_isIID (μ := μ) (W := W) hW) hshiftMean
  filter_upwards [hW.ae_elliptic, hprefix] with ω hω hω_prefix
  have hseries :
      (∑' n : ℕ,
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ₊[W](i + 1) ω))) = ∞ :=
    expSeries_eq_top_of_not_tendsto_atBot hω_prefix
  have hp0_pos : 0 < ((W ω).rightJumpProb 0 : ℝ) := by
    exact_mod_cast hω.pos 0
  have hc_pos : 0 < ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)⁻¹) := by
    refine ENNReal.ofReal_pos.mpr ?_
    positivity
  have hterms :
      (fun n : ℕ ↦ (blockedAtZeroEdgeConductance (W ω) n)⁻¹) =
        fun n : ℕ ↦
          ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)⁻¹) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ logρ₊[W](i + 1) ω)) := by
    funext n
    simpa using blockedAtZeroEdgeConductance_inv_eq_ofReal_exp_prefixSum (W := W) ω hω n
  rw [hterms, ENNReal.tsum_mul_left, hseries]
  exact ENNReal.mul_top hc_pos.ne'

/-- Helper for Exercise 19.6.1: at zero mean the blocked edge-conductance series itself diverges
almost surely. -/
theorem ae_blockedAtZeroConductanceSeries_eq_top_of_integral_logRatio_eq_zero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, (∑' n, blockedAtZeroEdgeConductance (W ω) n) = ∞ := by
  have hshiftMean :
      ∫ ω, -logρ₊[W](1) ω ∂μ = 0 := by
    rw [integral_neg, show ∫ ω, logρ₊[W](1) ω ∂μ = ∫ ω, logρ₊[W](0) ω ∂μ by
      simpa using (IsHalfLineSolomonEnvironmentLaw.identDistrib_logRatio hW 1 0).integral_eq,
      hmean, neg_zero]
  have hprefix :=
    ae_not_tendsto_atBot_prefixSum_of_mean_zero
      (μ := μ) (Y := fun n ↦ fun ω ↦ -logρ₊[W](n + 1) ω)
      ((IsHalfLineSolomonEnvironmentLaw.integrable_logRatio hW hlog 1).neg)
      (isIID_neg (μ := μ) (shiftedLogRatio_isIID (μ := μ) (W := W) hW))
      hshiftMean
  filter_upwards [hW.ae_elliptic, hprefix] with ω hω hω_prefix
  have hseries :
      (∑' n : ℕ,
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ₊[W](i + 1) ω))) = ∞ :=
    expSeries_eq_top_of_not_tendsto_atBot hω_prefix
  have hp0_pos : 0 < ((W ω).rightJumpProb 0 : ℝ) := by
    exact_mod_cast hω.pos 0
  have hc_pos : 0 < ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) := by
    exact ENNReal.ofReal_pos.mpr hp0_pos
  have hterms :
      (fun n : ℕ ↦ blockedAtZeroEdgeConductance (W ω) n) =
        fun n : ℕ ↦
          ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ₊[W](i + 1) ω)) := by
    funext n
    calc
      blockedAtZeroEdgeConductance (W ω) n
          = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
              ENNReal.ofReal
                (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
                  exact blockedAtZeroEdgeConductance_eq_ofReal_exp_negPrefixSum (W := W) ω hω n
      _ = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ₊[W](i + 1) ω)) := by
            congr 2
            rw [← Finset.sum_neg_distrib]
  rw [hterms, ENNReal.tsum_mul_left, hseries]
  exact ENNReal.mul_top hc_pos.ne'

/-- Helper for Exercise 19.6.1: positive mean makes the blocked edge-conductance series summable
almost surely. -/
theorem ae_blockedAtZeroConductanceSeries_lt_top_of_integral_logRatio_gt_zero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ₊[W](0) ω ∂μ) :
    ∀ᵐ ω ∂μ, (∑' n, blockedAtZeroEdgeConductance (W ω) n) < ∞ := by
  have hshiftMean :
      ∫ ω, -logρ₊[W](1) ω ∂μ < 0 := by
    rw [integral_neg, show ∫ ω, logρ₊[W](1) ω ∂μ = ∫ ω, logρ₊[W](0) ω ∂μ by
      simpa using (IsHalfLineSolomonEnvironmentLaw.identDistrib_logRatio hW 1 0).integral_eq]
    linarith
  have hprefix :=
    ae_eventually_prefixSum_le_halfMean_mul_of_mean_neg
      (μ := μ) (Y := fun n ↦ fun ω ↦ -logρ₊[W](n + 1) ω)
      ((IsHalfLineSolomonEnvironmentLaw.integrable_logRatio hW hlog 1).neg)
      (isIID_neg (μ := μ) (shiftedLogRatio_isIID (μ := μ) (W := W) hW))
      hshiftMean
  have hcoeff : (∫ ω, -logρ₊[W](1) ω ∂μ) / 2 < 0 := by
    linarith
  filter_upwards [hW.ae_elliptic, hprefix] with ω hω hω_prefix
  have hseries :
      (∑' n : ℕ,
        ENNReal.ofReal
          (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ₊[W](i + 1) ω))) < ∞ :=
    expSeries_lt_top_of_eventually_linearUpperBound hcoeff hω_prefix
  have hterms :
      (fun n : ℕ ↦ blockedAtZeroEdgeConductance (W ω) n) =
        fun n : ℕ ↦
          ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ₊[W](i + 1) ω)) := by
    funext n
    calc
      blockedAtZeroEdgeConductance (W ω) n
          = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
              ENNReal.ofReal
                (Real.exp (-Finset.sum (Finset.range n) (fun i : ℕ ↦ logρ₊[W](i + 1) ω))) := by
                  exact blockedAtZeroEdgeConductance_eq_ofReal_exp_negPrefixSum (W := W) ω hω n
      _ = ENNReal.ofReal (((W ω).rightJumpProb 0 : ℝ)) *
            ENNReal.ofReal
              (Real.exp (Finset.sum (Finset.range n) fun i : ℕ ↦ -logρ₊[W](i + 1) ω)) := by
            congr 2
            rw [← Finset.sum_neg_distrib]
  rw [hterms, ENNReal.tsum_mul_left]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hseries

/-- Helper for Exercise 19.6.1: in an elliptic environment, every blocked conductance row weight
is strictly positive. -/
theorem blockedAtZeroConductance_vertexWeight_pos
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (x : ℕ) :
    0 < conductance (blockedAtZeroConductance W) x := by
  cases x with
  | zero =>
      -- Proof comment: the boundary row weight is exactly `1`.
      simpa [blockedAtZeroConductance_vertexWeight_zero]
  | succ n =>
      -- Proof comment: the interior row weight already contains the positive left-edge
      -- conductance.
      rw [blockedAtZeroConductance_vertexWeight_succ]
      exact lt_of_lt_of_le (blockedAtZeroEdgeConductance_pos hW n)
        (le_add_of_nonneg_right (zero_le _))

/-- Helper for Exercise 19.6.1: in an elliptic environment, every blocked conductance row weight
is finite. -/
theorem blockedAtZeroConductance_vertexWeight_lt_top
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (x : ℕ) :
    conductance (blockedAtZeroConductance W) x < ∞ := by
  cases x with
  | zero =>
      -- Proof comment: the boundary row weight is the finite value `1`.
      simpa [blockedAtZeroConductance_vertexWeight_zero]
  | succ n =>
      -- Proof comment: the interior row weight is the sum of two finite adjacent edge
      -- conductances.
      rw [blockedAtZeroConductance_vertexWeight_succ]
      exact ENNReal.add_lt_top.2
        ⟨lt_of_le_of_ne le_top (blockedAtZeroEdgeConductance_ne_top hW n),
          lt_of_le_of_ne le_top (blockedAtZeroEdgeConductance_ne_top hW (n + 1))⟩

/-- Helper for Exercise 19.6.1: the blocked conductance measure is nonzero because it gives
singleton mass `1` to the boundary state `0`. -/
theorem blockedAtZeroConductanceMeasure_ne_zero (W : HalfLineRandomEnvironment) :
    (conductanceMeasure (blockedAtZeroConductance W) : Measure ℕ) ≠ 0 := by
  intro hzero
  have hsingleton :
      conductanceMeasure (blockedAtZeroConductance W) ({0} : Set ℕ) = 0 := by
    simpa using congrArg (fun ν : Measure ℕ ↦ ν ({0} : Set ℕ)) hzero
  -- Proof comment: the boundary singleton already has mass `1`, so the whole measure cannot
  -- vanish.
  simpa [conductanceMeasure_apply_singleton, blockedAtZeroConductance_vertexWeight_zero] using
    hsingleton

/-- Helper for Exercise 19.6.1: the total mass of the blocked conductance measure is the series of
all row weights. -/
theorem blockedAtZeroConductanceMeasure_univ_eq_tsum
    (W : HalfLineRandomEnvironment) :
    conductanceMeasure (blockedAtZeroConductance W) Set.univ =
      ∑' x : ℕ, conductance (blockedAtZeroConductance W) x := by
  -- Proof comment: integrate the constant function `1` against the conductance measure and unfold
  -- the Dirac-sum expansion from Example 19.10.
  calc
    conductanceMeasure (blockedAtZeroConductance W) Set.univ
        = ∫⁻ x, (1 : ℝ≥0∞) ∂ conductanceMeasure (blockedAtZeroConductance W) := by
            simp
    _ = ∑' x : ℕ, conductance (blockedAtZeroConductance W) x * 1 := by
          simpa using
            (lintegral_conductanceMeasure (C := blockedAtZeroConductance W)
              (f := fun _ : ℕ ↦ (1 : ℝ≥0∞)))
    _ = ∑' x : ℕ, conductance (blockedAtZeroConductance W) x := by simp

/-- Helper for Exercise 19.6.1: the total mass of the blocked conductance measure splits into the
boundary row weight and the interior row-weight tail. -/
theorem blockedAtZeroConductanceMeasure_univ_eq
    (W : HalfLineRandomEnvironment) :
    conductanceMeasure (blockedAtZeroConductance W) Set.univ =
      conductance (blockedAtZeroConductance W) 0 +
        ∑' n : ℕ, conductance (blockedAtZeroConductance W) (n + 1) := by
  let f : ℕ → ℝ≥0∞ := fun n ↦ conductance (blockedAtZeroConductance W) n
  calc
    conductanceMeasure (blockedAtZeroConductance W) Set.univ
        = ∑' x : ℕ, f x :=
          blockedAtZeroConductanceMeasure_univ_eq_tsum W
    _ = f 0 + ∑' n : ℕ, f (n + 1) := by
          simpa [f] using (tsum_eq_zero_add' ENNReal.summable (f := f))
    _ = conductance (blockedAtZeroConductance W) 0 +
          ∑' n : ℕ, conductance (blockedAtZeroConductance W) (n + 1) := by
          simp [f]

/-- Helper for Exercise 19.6.1: finiteness of the blocked edge-conductance series makes the total
mass of the reversible conductance measure finite. -/
theorem blockedAtZeroConductanceMeasure_univ_lt_top_of_series_lt_top
    (W : HalfLineRandomEnvironment)
    (hseries : (∑' n, blockedAtZeroEdgeConductance W n) < ∞) :
    conductanceMeasure (blockedAtZeroConductance W) Set.univ < ∞ := by
  let c : ℕ → ℝ≥0∞ := blockedAtZeroEdgeConductance W
  have htail_lt_top : (∑' n : ℕ, c (n + 1)) < ∞ := by
    calc
      (∑' n : ℕ, c (n + 1))
          ≤ c 0 + ∑' n : ℕ, c (n + 1) := by
              exact le_add_of_nonneg_left (zero_le _)
      _ = ∑' n : ℕ, c n := by
            simpa using (tsum_eq_zero_add' ENNReal.summable (f := c)).symm
      _ < ∞ := hseries
  have hrows_lt_top :
      (∑' n : ℕ, conductance (blockedAtZeroConductance W) (n + 1)) < ∞ := by
    rw [show (fun n : ℕ ↦ conductance (blockedAtZeroConductance W) (n + 1)) =
        fun n : ℕ ↦ c n + c (n + 1) by
          funext n
          simp [c, blockedAtZeroConductance_vertexWeight_succ]]
    rw [ENNReal.tsum_add]
    exact ENNReal.add_lt_top.2 ⟨hseries, htail_lt_top⟩
  -- Proof comment: the boundary row contributes `1`, and the interior rows split into the
  -- original edge-conductance series plus its one-step tail.
  calc
    conductanceMeasure (blockedAtZeroConductance W) Set.univ
        = conductance (blockedAtZeroConductance W) 0 +
            ∑' n : ℕ, conductance (blockedAtZeroConductance W) (n + 1) :=
          blockedAtZeroConductanceMeasure_univ_eq W
    _ < ∞ := by
          refine ENNReal.add_lt_top.2 ⟨?_, hrows_lt_top⟩
          simpa [blockedAtZeroConductance_vertexWeight_zero]

/-- Helper for Exercise 19.6.1: if the reversible conductance measure has finite total mass, then
the blocked edge-conductance series is summable. -/
theorem blockedAtZeroConductanceSeries_lt_top_of_conductanceMeasure_univ_lt_top
    (W : HalfLineRandomEnvironment)
    (hmeasure : conductanceMeasure (blockedAtZeroConductance W) Set.univ < ∞) :
    (∑' n, blockedAtZeroEdgeConductance W n) < ∞ := by
  have hrows_lt_top :
      (∑' n : ℕ, conductance (blockedAtZeroConductance W) n) < ∞ := by
    simpa [blockedAtZeroConductanceMeasure_univ_eq_tsum W] using hmeasure
  have hterm_le :
      ∀ n : ℕ,
        blockedAtZeroEdgeConductance W n ≤ conductance (blockedAtZeroConductance W) n := by
    intro n
    cases n with
    | zero =>
        -- Proof comment: at the boundary the edge conductance is the right-jump probability, hence
        -- bounded by the total row weight `1`.
        simpa [blockedAtZeroEdgeConductance_zero, blockedAtZeroConductance_vertexWeight_zero] using
          (show (W.rightJumpProb 0 : ℝ≥0∞) ≤ 1 by
            exact_mod_cast W.rightJumpProb_le_one 0)
    | succ n =>
        -- Proof comment: at interior sites the row weight contains the right-edge conductance as a
        -- summand.
        rw [blockedAtZeroConductance_vertexWeight_succ]
        exact le_add_of_nonneg_left (zero_le _)
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum hterm_le) hrows_lt_top

/-- Helper for Exercise 19.6.1: every positive state of the blocked half-line chain is hit with
strictly positive probability when starting from `0`. -/
theorem blockedAtZeroEverHitsProbability_pos_from_zero
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) (n : ℕ) :
    0 < (F[P, X]) 0 (n + 1) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  have hmass :
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ (n + 1)) 0)
          ({n + 1} : Set ℕ) := by
    simpa [Nat.zero_add] using
      blockedAtZeroRightPathMass_pos (W := W) hW 0 (n + 1)
  have hstep :
      0 < (P 0 : Measure Ξ) {ξ | X (n + 1) ξ = n + 1} := by
    have hpreimage :
        {ξ | X (n + 1) ξ = n + 1} = X (n + 1) ⁻¹' ({n + 1} : Set ℕ) := by
      ext ξ
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process (n + 1)) (measurableSet_singleton (n + 1))]
    rw [hReal.transition_eq 0 (n + 1)]
    simpa using hmass
  have hsubset :
      {ξ | X (n + 1) ξ = n + 1} ⊆ {ξ | ∃ m : ℕ, 0 < m ∧ X m ξ = n + 1} := by
    intro ξ hξ
    exact ⟨n + 1, Nat.succ_pos _, hξ⟩
  have hhit_enn :
      0 < (P 0 : Measure Ξ) {ξ | ∃ m : ℕ, 0 < m ∧ X m ξ = n + 1} := by
    exact lt_of_lt_of_le hstep (measure_mono hsubset)
  -- Proof comment: the positive-time visit event contains the explicit monotone rightward path
  -- event with strictly positive mass.
  rw [everHitsProbability_def]
  exact ENNReal.toReal_pos hhit_enn.ne' (measure_ne_top _ _)

/-- Helper for Exercise 19.6.1: every positive state of the blocked half-line chain hits `0`
with strictly positive probability. -/
theorem blockedAtZeroEverHitsProbability_pos_to_zero
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) (n : ℕ) :
    0 < (F[P, X]) (n + 1) 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  have hmass :
      0 <
        ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ (n + 1))
          (n + 1)) ({0} : Set ℕ) := by
    simpa [Nat.zero_add] using
      blockedAtZeroLeftPathMass_pos (W := W) hW 0 (n + 1)
  have hstep :
      0 < (P (n + 1) : Measure Ξ) {ξ | X (n + 1) ξ = 0} := by
    have hpreimage :
        {ξ | X (n + 1) ξ = 0} = X (n + 1) ⁻¹' ({0} : Set ℕ) := by
      ext ξ
      simp
    rw [hpreimage]
    rw [← Measure.map_apply (hReal.measurable_process (n + 1)) (measurableSet_singleton 0)]
    rw [hReal.transition_eq (n + 1) (n + 1)]
    simpa using hmass
  have hsubset :
      {ξ | X (n + 1) ξ = 0} ⊆ {ξ | ∃ m : ℕ, 0 < m ∧ X m ξ = 0} := by
    intro ξ hξ
    exact ⟨n + 1, Nat.succ_pos _, hξ⟩
  have hhit_enn :
      0 < (P (n + 1) : Measure Ξ) {ξ | ∃ m : ℕ, 0 < m ∧ X m ξ = 0} := by
    exact lt_of_lt_of_le hstep (measure_mono hsubset)
  -- Proof comment: the explicit monotone leftward path event sits inside the positive-time hit
  -- event of `0`.
  rw [everHitsProbability_def]
  exact ENNReal.toReal_pos hhit_enn.ne' (measure_ne_top _ _)

/-- Helper for Exercise 19.6.1: once state `0` is recurrent, recurrence propagates to every state
of the blocked half-line chain by positive communication from the boundary. -/
theorem blockedAtZeroAllStatesRecurrent_of_stateZeroRecurrent
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic)
    (hrec0 : IsRecurrentState P X 0) :
    ∀ x : ℕ, IsRecurrentState P X x := by
  intro x
  cases x with
  | zero =>
      -- Proof comment: the boundary state is the given recurrent base case.
      simpa using hrec0
  | succ n =>
      have hhit :
          0 < (F[P, X]) 0 (n + 1) :=
        blockedAtZeroEverHitsProbability_pos_from_zero (P := P) (X := X) (W := W) hW n
      -- Proof comment: Theorem 17.35 transports recurrence from `0` to any state that is reached
      -- with positive ever-hit probability.
      exact
        isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
          (κ := fun m : ℕ ↦
            discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ m)
          (P := P) (X := X) hrec0 hhit

/-- Helper for Exercise 19.6.1: after transporting the blocked walk to its conductance
presentation, recurrence of `0` is equivalent to infinite effective resistance to infinity. -/
theorem blockedAtZeroStateZeroRecurrent_iff_effectiveResistanceToInfinity_eq_top
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) :
    IsRecurrentState P X 0 ↔
      effectiveResistanceToInfinity (blockedAtZeroConductance W) P X 0 = ∞ := by
  letI :
      IsRandomWalkWithWeights
        (conductanceTransitionMatrix (blockedAtZeroConductance W))
        (blockedAtZeroConductance W) :=
    conductanceTransitionMatrix_isRandomWalkWithWeights
      (C := blockedAtZeroConductance W)
      (blockedAtZeroConductance_symmetric W)
      (blockedAtZeroConductance_vertexWeight_lt_top hW)
      (blockedAtZeroConductance_vertexWeight_pos hW)
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel (conductanceTransitionMatrix (blockedAtZeroConductance W)) ^ n)
        P X :=
    isMarkovProcessRealization_blockedAtZeroConductance
      (W := W) (P := P) (X := X) hW
  -- Proof comment: the generic Chapter 19 recurrence criterion applies once the blocked kernel is
  -- rewritten as its normalized conductance walk.
  exact
    isRecurrentState_iff_effectiveResistanceToInfinity_eq_top
      (p := conductanceTransitionMatrix (blockedAtZeroConductance W))
      (C := blockedAtZeroConductance W) (P := P) (X := X) (x₁ := 0)

/-- Helper for Exercise 19.6.1: from the blocked boundary state `0`, the one-step mass at the
right neighbor `1` is exactly the owner right-jump probability. -/
private theorem blockedAtZeroOneStep_one_prob_eq_rightJumpProb
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X] :
    (P 0 : Measure Ξ) {ω | X 1 ω = 1} = W.rightJumpProb 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  have hpreimage : {ω | X 1 ω = 1} = X 1 ⁻¹' ({1} : Set ℕ) := by
    ext ω
    simp
  -- Proof comment: read the time-`1` singleton event through the one-step transition row at `0`.
  rw [hpreimage]
  rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton 1)]
  rw [hReal.transition_eq 0 1, pow_one, discreteMatrixKernel_apply_singleton]
  simpa [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one]

/-- Helper for Exercise 19.6.1: from the blocked boundary state `0`, the one-step self-loop mass
is the blocked boundary probability `1 - W.rightJumpProb 0`. -/
private theorem blockedAtZeroOneStep_zero_prob_eq_selfLoopMass
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X] :
    (P 0 : Measure Ξ) {ω | X 1 ω = 0} = (1 : ℝ≥0∞) - W.rightJumpProb 0 := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  have hpreimage : {ω | X 1 ω = 0} = X 1 ⁻¹' ({0} : Set ℕ) := by
    ext ω
    simp
  -- Proof comment: the blocked self-loop mass is the singleton row-entry at `0`.
  rw [hpreimage]
  rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton 0)]
  rw [hReal.transition_eq 0 1, pow_one, discreteMatrixKernel_apply_singleton]
  simpa [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self]

/-- Helper for Exercise 19.6.1: the first blocked prefix-resistance reciprocal is the boundary
right-jump probability. -/
private theorem blockedAtZeroInvPrefixResistance_zero
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) :
    (Finset.sum (Finset.range 1) fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹ =
      W.rightJumpProb 0 := by
  have hp0_ne_zero : (W.rightJumpProb 0 : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (hW.pos 0).ne'
  -- Proof comment: the prefix of length `1` contains only the boundary edge conductance `c₀`.
  simpa [blockedAtZeroEdgeConductance_zero, hp0_ne_zero] using
    (ENNReal.inv_inv (W.rightJumpProb 0 : ℝ≥0∞))

/-- Helper for Exercise 19.6.1: under `P x`, the blocked half-line realization starts from `x`
almost surely. -/
private theorem blockedAtZeroInitialState_ae_eq_start
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (x : ℕ) :
    ∀ᵐ ω ∂(P x : Measure Ξ), X 0 ω = x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  have hprob : (P x : Measure Ξ) (X 0 ⁻¹' ({x} : Set ℕ)) = 1 := by
    have hInit := congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) (hReal.initial_eq x)
    simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit
  have hmeas : MeasurableSet (X 0 ⁻¹' ({x} : Set ℕ)) := by
    simpa using (hReal.measurable_process 0) (measurableSet_singleton x)
  exact (mem_ae_iff_prob_eq_one hmeas).2 hprob

/-- Helper for Exercise 19.6.1: if the realized path starts outside `A`, then the first hit
searched from time `0` agrees with the first hit searched from time `1`. -/
private theorem blockedAtZeroHittingAfter_zero_eq_one_of_not_mem_initial
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    {A : Set ℕ} {ω : Ξ} (h0 : X 0 ω ∉ A) :
    hittingAfter X A 0 ω = hittingAfter X A 1 ω := by
  -- Proof comment: monotonicity gives the easy direction, and `h0` rules out a time-`0` hit.
  refine le_antisymm (hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)) ?_
  by_cases htop : hittingAfter X A 0 ω = ⊤
  · have hle :
        hittingAfter X A 0 ω ≤ hittingAfter X A 1 ω :=
      hittingAfter_apply_mono (u := X) (s := A) (ω := ω) (by simp)
    simpa [htop] using hle
  · lift hittingAfter X A 0 ω to ℕ using htop with n hn
    have hn_ne_top : hittingAfter X A 0 ω ≠ ⊤ := by
      rw [← hn]
      simp
    have hidx : (hittingAfter X A 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hmem : X n ω ∈ A := by
      -- Proof comment: a finite first entrance time necessarily lands inside the target set.
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := X) (s := A) (n := 0) (ω := ω) hn_ne_top
    have hn_pos : 1 ≤ n := by
      by_contra hn_pos
      have hn_zero : n = 0 := by omega
      exact h0 (hn_zero ▸ hmem)
    simpa [hn] using
      hittingAfter_le_of_mem (u := X) (s := A) (n := 1) (ω := ω) hn_pos hmem

/-- Helper for Exercise 19.6.1: the event that the first hit of `insert y A` occurs at `y`. -/
private def firstHitAtStateEvent (X : ℕ → Ξ → ℕ) (A : Set ℕ) (y : ℕ) : Set Ξ :=
  {ω | hittingAfter X (insert y A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert y A) 0) ω = y}

/-- Helper for Exercise 19.6.1: the concrete first-hit event at `b` is exactly the owner event
used in `F_A`. -/
private theorem blockedAtZeroFirstHitEvent_real_eq_F_A
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    (A : Set ℕ) (z b : ℕ) :
    (P z : Measure Ξ).real
        {ω |
          hittingAfter X (insert b A) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b A) 0) ω = b} =
      F_A P X A z b := by
  rw [F_A]
  -- Proof comment: the local blocked event has exactly the same concrete description as the
  -- owner event hidden inside `F_A`.
  rfl

/-- Helper for Exercise 19.6.1: off the two-point boundary `{0, N + 2}`, the positive-time
boundary-hit distribution landing at `N + 2` agrees with `F_A`. -/
private theorem blockedAtZeroBoundaryHitDistribution_eq_F_A_of_not_mem_boundary
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    {N x : ℕ} (hx : x ∉ ({0, N + 2} : Set ℕ)) :
    ((P x : Measure Ξ)
      {ω | hittingAfter X ({0, N + 2} : Set ℕ) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({0, N + 2} : Set ℕ) 1) ω = N + 2}).toReal =
      F_A P X ({0} : Set ℕ) x (N + 2) := by
  let μ : Measure Ξ := (P x : Measure Ξ)
  have hEventAE :
      {ω | hittingAfter X ({0, N + 2} : Set ℕ) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({0, N + 2} : Set ℕ) 1) ω = N + 2} =ᵐ[μ]
        firstHitAtStateEvent X ({0} : Set ℕ) (N + 2) := by
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = x :=
      blockedAtZeroInitialState_ae_eq_start (W := W) (P := P) (X := X) x
    filter_upwards [hstart] with ω hω
    have hx0 : X 0 ω ∉ ({0, N + 2} : Set ℕ) := by
      simpa [hω] using hx
    have hτeq :
        hittingAfter X ({0, N + 2} : Set ℕ) 0 ω =
          hittingAfter X ({0, N + 2} : Set ℕ) 1 ω :=
      blockedAtZeroHittingAfter_zero_eq_one_of_not_mem_initial (W := W) (P := P) (X := X) hx0
    have hboundary : ({0, N + 2} : Set ℕ) = insert (N + 2) ({0} : Set ℕ) := by
      ext ξ
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
    have hτeq' :
        hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0 ω =
          hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1 ω := by
      simpa [hboundary] using hτeq
    have hleft :
        {ω | hittingAfter X ({0, N + 2} : Set ℕ) 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X ({0, N + 2} : Set ℕ) 1) ω = N + 2} ω ↔
          {ω | hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1) ω = N + 2} ω := by
      simpa [hboundary]
    have hright :
        {ω | hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1) ω = N + 2} ω ↔
          {ω | hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω = N + 2} ω := by
      have hstopEq :
          stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω =
            stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1) ω := by
        rw [stoppedValue, hτeq']
        rfl
      constructor
      · rintro ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.trans hstop
      · rintro ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq'] using hfin
        · exact hstopEq.symm.trans hstop
  -- Proof comment: away from the boundary, the time-`1` and time-`0` descriptions coincide.
    exact propext (hleft.trans hright)
  rw [measure_congr hEventAE]
  simpa [Measure.real_def, firstHitAtStateEvent] using
    blockedAtZeroFirstHitEvent_real_eq_F_A (P := P) (X := X) ({0} : Set ℕ) x (N + 2)

/-- Helper for Exercise 19.6.1: on the boundary `{0, N + 2}`, the first-hit surface `F_A`
already has the Dirichlet boundary values. -/
private theorem blockedAtZeroFA_eq_boundaryDatum_on_boundary
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (N x : ℕ) (hx : x ∈ ({0, N + 2} : Set ℕ)) :
    F_A P X ({0} : Set ℕ) x (N + 2) = if x = N + 2 then 1 else 0 := by
  by_cases hRight : x = N + 2
  · subst hRight
    let μ : Measure Ξ := (P (N + 2) : Measure Ξ)
    let S : Set Ξ := {ω | X 0 ω = N + 2}
    have hStart : μ S = 1 := by
      have hS_meas : MeasurableSet S := by
        let hReal :
            IsMarkovProcessRealization
              (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
              P X := inferInstance
        simpa [S, Set.preimage] using hReal.measurable_process 0 (measurableSet_singleton (N + 2))
      exact
        (mem_ae_iff_prob_eq_one hS_meas).1 <|
          by simpa [S] using
            blockedAtZeroInitialState_ae_eq_start (W := W) (P := P) (X := X) (N + 2)
    have hSubset : S ⊆ firstHitAtStateEvent X ({0} : Set ℕ) (N + 2) := by
      intro ω hω
      have hτ0 :
          hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0 ω = 0 := by
        refine le_antisymm ?_
          (le_hittingAfter (u := X) (s := insert (N + 2) ({0} : Set ℕ)) (n := 0) ω)
        have hmem : X 0 ω ∈ insert (N + 2) ({0} : Set ℕ) := by
          left
          simpa [S] using hω
        exact hittingAfter_le_of_mem (u := X) (s := insert (N + 2) ({0} : Set ℕ))
          (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω = X 0 ω := by
        simp [stoppedValue, hτ0]
      constructor
      · simpa [firstHitAtStateEvent, hτ0]
      · simpa [firstHitAtStateEvent, hτ0] using hstop.trans hω
    have hEvent :
        μ (firstHitAtStateEvent X ({0} : Set ℕ) (N + 2)) = 1 := by
      refine le_antisymm ?_ ?_
      · calc
          μ (firstHitAtStateEvent X ({0} : Set ℕ) (N + 2)) ≤ μ Set.univ := by
              exact measure_mono (by intro ω hω; simp)
          _ = 1 := by simp [μ]
      · calc
          1 = μ S := hStart.symm
          _ ≤ μ (firstHitAtStateEvent X ({0} : Set ℕ) (N + 2)) := measure_mono hSubset
    -- Proof comment: starting at `N + 2` forces the first boundary hit to be `N + 2` at time
    -- `0`, so `F_A` takes the right boundary value `1`.
    simpa [F_A, Measure.real_def, μ] using congrArg ENNReal.toReal hEvent
  · have hZero : x = 0 := by
      rcases (by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with hZero | hTail
      · exact hZero
      · exact False.elim (hRight hTail)
    subst hZero
    let μ : Measure Ξ := (P 0 : Measure Ξ)
    let S : Set Ξ := {ω | X 0 ω = 0}
    have hSubset :
        firstHitAtStateEvent X ({0} : Set ℕ) (N + 2) ⊆ Sᶜ := by
      intro ω hω
      simp only [Set.mem_compl_iff, S]
      intro hSω
      have hτ0 :
          hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0 ω = 0 := by
        refine le_antisymm ?_
          (le_hittingAfter (u := X) (s := insert (N + 2) ({0} : Set ℕ)) (n := 0) ω)
        have hmem : X 0 ω ∈ insert (N + 2) ({0} : Set ℕ) := by
          right
          simpa [S] using hSω
        exact hittingAfter_le_of_mem (u := X) (s := insert (N + 2) ({0} : Set ℕ))
          (n := 0) (ω := ω) (by simp) hmem
      have hstop :
          stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω = 0 := by
        calc
          stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω = X 0 ω := by
            simp [stoppedValue, hτ0]
          _ = 0 := hSω
      have : 0 = N + 2 := hstop.symm.trans hω.2
      omega
    have hS_meas : MeasurableSet S := by
      let hReal :
          IsMarkovProcessRealization
            (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
            P X := inferInstance
      simpa [S, Set.preimage] using hReal.measurable_process 0 (measurableSet_singleton 0)
    have hStart : μ S = 1 := by
      exact
        (mem_ae_iff_prob_eq_one hS_meas).1 <|
          by simpa [S] using
            blockedAtZeroInitialState_ae_eq_start (W := W) (P := P) (X := X) 0
    have hSComplZero : μ Sᶜ = 0 := by
      rw [measure_compl hS_meas (by rw [hStart]; simp), hStart]
      norm_num
    have hEventZero :
        μ (firstHitAtStateEvent X ({0} : Set ℕ) (N + 2)) = 0 := by
      exact measure_mono_null hSubset hSComplZero
    -- Proof comment: starting at `0`, the time-`0` boundary hit is already `0`, so the first-hit
    -- event at `N + 2` is null.
    simpa [F_A, Measure.real_def, μ, hRight] using congrArg ENNReal.toReal hEventZero

/-- Helper for Exercise 19.6.1: the blocked walk induces a canonical path-law kernel on
`ℕ → ℕ` by pushing forward each start law along the realized trajectory. -/
private def blockedAtZeroRealizationPathKernel
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ} :
    Kernel ℕ (ℕ → ℕ) :=
  Kernel.ofFunOfCountable fun x ↦
    (P x : Measure Ξ).map (fun ω : Ξ ↦ fun n : ℕ ↦ X n ω)

/-- Helper for Exercise 19.6.1: each row of the blocked path-law kernel is the pushforward of the
corresponding start law along the realized path. -/
@[simp] private theorem blockedAtZeroRealizationPathKernel_apply
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    (x : ℕ) :
    blockedAtZeroRealizationPathKernel (P := P) (X := X) x =
      (P x : Measure Ξ).map (fun ω : Ξ ↦ fun n : ℕ ↦ X n ω) := rfl

/-- Helper for Exercise 19.6.1: the blocked path-law kernel recovers the original `n`-step
transition row when read at time `n`. -/
private theorem blockedAtZeroRealizationPathKernel_transition
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (x n : ℕ) :
    transitionKernel (blockedAtZeroRealizationPathKernel (P := P) (X := X)) n x =
      (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  -- Proof comment: the `n`-th coordinate of the path pushforward is exactly the time-`n`
  -- marginal of the original realization.
  rw [transitionKernel_apply]
  change
    Measure.map (fun ξ : ℕ → ℕ ↦ ξ n)
      ((P x : Measure Ξ).map (fun ω : Ξ ↦ fun m : ℕ ↦ X m ω)) =
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · refine measurable_pi_lambda _ fun m ↦ ?_
    exact hReal.measurable_process m

/-- Helper for Exercise 19.6.1: the blocked path-law kernel makes the realization into a
time-homogeneous Markov process on path space. -/
private theorem blockedAtZeroRealizationPathKernel_isTimeHomogeneousMarkovProcess
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X] :
    IsTimeHomogeneousMarkovProcess X P
      (blockedAtZeroRealizationPathKernel (P := P) (X := X)) := by
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := ?_
      path_law := ?_
      markov_property := ?_ }
  · intro x
    have hprob :
        (P x : Measure Ξ) (X 0 ⁻¹' ({x} : Set ℕ)) = 1 := by
      have hInit := congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) (hReal.initial_eq x)
      simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using
        hInit
    exact hprob
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: rewrite the path-kernel transition back to the original realization
    -- transition kernel before applying the realization Markov property.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [blockedAtZeroRealizationPathKernel_transition (W := W) (P := P) (X := X) (x := X s ω) t]

/-- Helper for Exercise 19.6.1: finite prefix avoidance of a boundary set is measurable on the
blocked path space `ℕ → ℕ`. -/
private theorem blockedAtZeroAvoidBeforePathEvent_measurable
    (B : Set ℕ) :
    ∀ n : ℕ, MeasurableSet {ξ : ℕ → ℕ | ∀ m < n, ξ m ∉ B}
  | 0 => by
      simp
  | n + 1 => by
      have hEq :
          {ξ : ℕ → ℕ | ∀ m < n + 1, ξ m ∉ B} =
            {ξ : ℕ → ℕ | ∀ m < n, ξ m ∉ B} ∩ {ξ : ℕ → ℕ | ξ n ∉ B} := by
        ext ξ
        constructor
        · intro hξ
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hξ m (Nat.lt_succ_of_lt hm)
          · exact hξ n (Nat.lt_succ_self n)
        · intro hξ m hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
          · exact hξ.1 m hm
          · exact hξ.2
      -- Proof comment: split length `n + 1` avoidance into the previous prefix and the new
      -- coordinate constraint at time `n`.
      rw [hEq]
      refine (blockedAtZeroAvoidBeforePathEvent_measurable B n).inter ?_
      change MeasurableSet (((fun ξ : ℕ → ℕ ↦ ξ n) ⁻¹' Bᶜ))
      exact
        (measurable_pi_apply n)
          (by simpa using (MeasurableSet.of_discrete : MeasurableSet B))

/-- Helper for Exercise 19.6.1: on path space, first hitting `insert b A` at `b` means reaching
`b` at some witness time while avoiding the full boundary earlier. -/
private def blockedAtZeroFirstHitPathEvent (A : Set ℕ) (b : ℕ) : Set (ℕ → ℕ) :=
  {ξ | ∃ n : ℕ, ξ n = b ∧ ∀ m < n, ξ m ∉ insert b A}

/-- Helper for Exercise 19.6.1: the blocked path-space first-hit event is measurable. -/
private theorem blockedAtZeroFirstHitPathEvent_measurable
    (A : Set ℕ) (b : ℕ) :
    MeasurableSet (blockedAtZeroFirstHitPathEvent A b) := by
  have hEq :
      blockedAtZeroFirstHitPathEvent A b =
        ⋃ n : ℕ,
          ({ξ : ℕ → ℕ | ξ n = b} ∩ {ξ : ℕ → ℕ | ∀ m < n, ξ m ∉ insert b A}) := by
    ext ξ
    simp [blockedAtZeroFirstHitPathEvent]
  rw [hEq]
  refine MeasurableSet.iUnion fun n ↦ ?_
  refine
    (show MeasurableSet {ξ : ℕ → ℕ | ξ n = b} from by
      change MeasurableSet (((fun ξ : ℕ → ℕ ↦ ξ n) ⁻¹' ({b} : Set ℕ)))
      exact (measurable_pi_apply n) (MeasurableSet.singleton b)).inter ?_
  exact blockedAtZeroAvoidBeforePathEvent_measurable (insert b A) n

/-- Helper for Exercise 19.6.1: the first-hit event is equivalent to an explicit witness time. -/
private theorem blockedAtZeroFirstHitEvent_iff_exists
    {Ω' : Type*} [MeasurableSpace Ω']
    (u : ℕ → Ω' → ℕ) (A : Set ℕ) (b : ℕ) (ω : Ω') :
    (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) ↔
      ∃ n : ℕ, u n ω = b ∧ ∀ m < n, u m ω ∉ insert b A := by
  let s : Set ℕ := insert b A
  constructor
  · rintro ⟨hfin, hstop⟩
    have hne_top : hittingAfter u s 0 ω ≠ ⊤ := ne_of_lt hfin
    lift hittingAfter u s 0 ω to ℕ using hne_top with n hn
    have hidx : (hittingAfter u s 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hnb : u n ω = b := by
      -- Proof comment: after naming the finite first-hit time, the stopped value is exactly the
      -- coordinate at that time.
      change stoppedValue u (hittingAfter u s 0) ω = b at hstop
      rw [stoppedValue, hidx] at hstop
      exact hstop
    refine ⟨n, hnb, ?_⟩
    intro m hm
    have hm_lt_hit : (m : ℕ∞) < hittingAfter u s 0 ω := by
      have hm_top : (m : ℕ∞) < (n : ℕ∞) := by
        simpa using hm
      rw [← hn]
      exact hm_top
    -- Proof comment: every strictly earlier time stays outside the full boundary `insert b A`.
    exact
      notMem_of_lt_hittingAfter (u := u) (s := s) (n := 0) (ω := ω) (k := m) hm_lt_hit
        (by simp)
  · rintro ⟨n, hnb, havoid⟩
    have hhit_le_n :
        hittingAfter u s 0 ω ≤ n :=
      hittingAfter_le_of_mem (u := u) (s := s) (n := 0) (i := n) (ω := ω) (by simp) <| by
        simp [s, hnb]
    have hne_top : hittingAfter u s 0 ω ≠ ⊤ := by
      intro htop
      simpa [htop] using hhit_le_n
    lift hittingAfter u s 0 ω to ℕ using hne_top with t ht
    have hidx : (hittingAfter u s 0 ω).untopA = t := by
      rw [← ht, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have htn : t ≤ n := by
      simpa using hhit_le_n
    have hne_top0 : hittingAfter u s 0 ω ≠ ⊤ := by
      intro htop
      have ht_top : (t : ℕ∞) = ⊤ := ht.trans htop
      simpa using ht_top
    have ht_mem : u t ω ∈ s := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := 0) (ω := ω) hne_top0
    have hnot_lt : ¬ t < n := by
      intro hlt
      exact (havoid t hlt) ht_mem
    have htn_eq : t = n := le_antisymm htn (not_lt.mp hnot_lt)
    have hltop : hittingAfter u s 0 ω < ⊤ := lt_top_iff_ne_top.mpr hne_top0
    refine ⟨hltop, ?_⟩
    -- Proof comment: the first boundary hit occurs exactly at the witness time `n`, so the
    -- stopped value is the prescribed state `b`.
    rw [stoppedValue, hidx, htn_eq]
    exact hnb

/-- Helper for Exercise 19.6.1: if the current state lies outside `insert b A`, then the first-hit
event from time `0` is the first-hit path event of the shifted future path. -/
private theorem blockedAtZeroFuturePath_mem_firstHitPathEvent_iff
    {Ω' : Type*} [MeasurableSpace Ω']
    (u : ℕ → Ω' → ℕ) (A : Set ℕ) (b : ℕ) {ω : Ω'}
    (hstart : u 0 ω ∉ insert b A) :
    natFuturePath u 1 ω ∈ blockedAtZeroFirstHitPathEvent A b ↔
      (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) := by
  rw [show
      (hittingAfter u (insert b A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert b A) 0) ω = b) ↔
      ∃ n : ℕ, u n ω = b ∧ ∀ m < n, u m ω ∉ insert b A from
        blockedAtZeroFirstHitEvent_iff_exists u A b ω]
  constructor
  · rintro ⟨n, hnb, havoid⟩
    refine ⟨n + 1, ?_, ?_⟩
    · simpa [natFuturePath, Nat.add_comm] using hnb
    · intro m hm
      cases m with
      | zero =>
          simpa using hstart
      | succ m =>
          have hm_lt : m < n := by
            simpa using hm
          simpa [natFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using havoid m hm_lt
  · rintro ⟨n, hnb, havoid⟩
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      exact hstart <| by simpa [hn0] using Or.inl hnb
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
    refine ⟨k, ?_, ?_⟩
    · simpa [natFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnb
    · intro m hm
      have hm' : m + 1 < k + 1 := Nat.succ_lt_succ hm
      simpa [natFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using havoid (m + 1) hm'

/-- Helper for Exercise 19.6.1: the shifted blocked future-path hit event averages against the
one-step kernel through the blocked path-law kernel. -/
private theorem blockedAtZeroFuturePathHit_real_eq_pathKernelAverage
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (B : Set (ℕ → ℕ)) (hB : MeasurableSet B) (y : ℕ) :
    (P y : Measure Ξ).real ((natFuturePath X 1) ⁻¹' B) =
      ∫ z,
        (blockedAtZeroRealizationPathKernel (P := P) (X := X) z).real B
          ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) y) := by
  let μ : Measure Ξ := (P y : Measure Ξ)
  let futureIndicator : Ξ → ℝ := fun ω ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) (natFuturePath X 1 ω)
  let rowMass : ℕ → ℝ := fun z ↦
    (blockedAtZeroRealizationPathKernel (P := P) (X := X) z).real B
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: compose the measurable path-event indicator with the measurable one-step
    -- shifted path map.
    exact (Measurable.indicator measurable_const hB).comp <|
      measurable_natFuturePath X hReal.measurable_process 1
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the future-path indicator takes only the values `0` and `1`.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : natFuturePath X 1 ω ∈ B
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  letI : IsTimeHomogeneousMarkovProcess X P
      (blockedAtZeroRealizationPathKernel (P := P) (X := X)) :=
    blockedAtZeroRealizationPathKernel_isTimeHomogeneousMarkovProcess
      (W := W) (P := P) (X := X)
  have hgenerated_le :
      generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ξ› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X 1]
    exact (measurable_pastPath X hReal.measurable_process 1).comap_le
  have hcondAE :
      MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator =ᵐ[μ]
        fun ω ↦ rowMass (X 1 ω) := by
    let g : (ℕ → ℕ) → ℝ := fun ξ ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
    have hg_meas : Measurable g := by
      -- Proof comment: `g` is the measurable indicator of the path event `B`.
      exact Measurable.indicator measurable_const hB
    have hg_bdd : Bornology.IsBounded (Set.range g) := by
      -- Proof comment: an indicator only takes the values `0` and `1`.
      simpa [g] using isBounded_range_indicator_one B
    have hAE :=
      natFuturePathCondExp_of_markovProcessNat
        (X := X) (P := P) (κ := blockedAtZeroRealizationPathKernel (P := P) (X := X))
        (hX_meas := hReal.measurable_process)
        (hX0 := fun z ↦ by
          have hInit := congrArg (fun ν : Measure ℕ ↦ ν ({z} : Set ℕ)) (hReal.initial_eq z)
          simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton z)] using
            hInit)
        (hpath := fun z ↦ blockedAtZeroRealizationPathKernel_apply (P := P) (X := X) z)
        y 1 g hg_meas hg_bdd
    -- Proof comment: specialize the future-path conditional expectation to the indicator of `B`.
    filter_upwards [hAE] with ω hω
    simpa [g, futureIndicator, rowMass, natFuturePath, MeasureTheory.integral_indicator_one, hB]
      using hω
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    -- Proof comment: integrate the conditional-expectation identity over the ambient start law.
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω,
              MeasureTheory.condExp (m := generatedFiltrationSpace X 1) μ futureIndicator ω
              ∂μ := by
                symm
                exact integral_condExp hgenerated_le
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            exact integral_congr_ae hcondAE
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ =
        ∫ z, rowMass z ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) y) := by
    -- Proof comment: the time-`1` marginal of the realization is the one-step transition row.
    calc
      ∫ ω, rowMass (X 1 ω) ∂μ = ∫ z, rowMass z ∂((P y : Measure Ξ).map (X 1)) := by
            simpa [μ] using
              (MeasureTheory.integral_map
                (μ := (P y : Measure Ξ))
                (φ := X 1)
                (f := rowMass)
                (hReal.measurable_process 1).aemeasurable
                (Measurable.of_discrete.aestronglyMeasurable)).symm
      _ = ∫ z, rowMass z ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ 1) y) := by
            rw [hReal.transition_eq y 1]
      _ = ∫ z, rowMass z ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) y) := by
            simp
  -- Proof comment: rewrite the shifted-path mass as an indicator integral, then pass it through
  -- the conditional-expectation bridge and the time-`1` marginal identity.
  calc
    (P y : Measure Ξ).real ((natFuturePath X 1) ⁻¹' B)
        = ∫ ω, futureIndicator ω ∂μ := by
            symm
            simpa [μ, futureIndicator] using
              (MeasureTheory.integral_indicator_one
                (μ := μ)
                (s := (natFuturePath X 1) ⁻¹' B)
                ((measurable_natFuturePath X hReal.measurable_process 1) hB))
    _ = ∫ ω, rowMass (X 1 ω) ∂μ := hfutureIntegral
    _ = ∫ z, rowMass z
          ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) y) :=
        htransitionIntegral

/-- Helper for Exercise 19.6.1: each blocked path-kernel row mass of the first-hit path event is
the corresponding first-hit probability `F_A`. -/
private theorem blockedAtZeroRealizationPathKernel_real_firstHitPathEvent_eq_F_A
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (A : Set ℕ) (b z : ℕ) :
    (blockedAtZeroRealizationPathKernel (P := P) (X := X) z).real
        (blockedAtZeroFirstHitPathEvent A b) =
      F_A P X A z b := by
  let path : Ξ → ℕ → ℕ := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    -- Proof comment: the full realized path map is measurable coordinatewise.
    refine measurable_pi_lambda _ fun n ↦ ?_
    let hReal :
        IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
          P X := inferInstance
    exact hReal.measurable_process n
  have hpreimage :
      path ⁻¹' blockedAtZeroFirstHitPathEvent A b =
        {ω |
          hittingAfter X (insert b A) 0 ω < ⊤ ∧
            stoppedValue X (hittingAfter X (insert b A) 0) ω = b} := by
    ext ω
    -- Proof comment: the path-space witness-time description is exactly the owner first-hit
    -- event after pulling the event back along the realized path.
    simp [path, blockedAtZeroFirstHitPathEvent, blockedAtZeroFirstHitEvent_iff_exists]
  calc
    (blockedAtZeroRealizationPathKernel (P := P) (X := X) z).real
        (blockedAtZeroFirstHitPathEvent A b)
        = (((P z : Measure Ξ).map path).real (blockedAtZeroFirstHitPathEvent A b)) := by
            rfl
    _ = (P z : Measure Ξ).real (path ⁻¹' blockedAtZeroFirstHitPathEvent A b) := by
          simpa using
            (MeasureTheory.map_measureReal_apply hpath_meas
              (blockedAtZeroFirstHitPathEvent_measurable A b))
    _ = F_A P X A z b := by
          simpa [hpreimage] using blockedAtZeroFirstHitEvent_real_eq_F_A (P := P) (X := X) A z b

/-- Helper for Exercise 19.6.1: away from the two-point boundary `{0, N + 2}`, the blocked
first-hit surface is the one-step average of its future values. -/
private theorem blockedAtZeroFA_average_eq_interior
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    {N n : ℕ} (hn : n ≤ N) :
    F_A P X ({0} : Set ℕ) (n + 1) (N + 2) =
      ∫ z, F_A P X ({0} : Set ℕ) z (N + 2)
        ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) (n + 1)) := by
  let μ : Measure Ξ := (P (n + 1) : Measure Ξ)
  let B : Set (ℕ → ℕ) := blockedAtZeroFirstHitPathEvent ({0} : Set ℕ) (N + 2)
  have hB : MeasurableSet B :=
    blockedAtZeroFirstHitPathEvent_measurable ({0} : Set ℕ) (N + 2)
  have hx :
      n + 1 ∉ ({0, N + 2} : Set ℕ) := by
    intro hx
    simp at hx
    omega
  have hEventAE :
      {ω | hittingAfter X ({0, N + 2} : Set ℕ) 1 ω < ⊤ ∧
          stoppedValue X (hittingAfter X ({0, N + 2} : Set ℕ) 1) ω = N + 2} =ᵐ[μ]
        ((natFuturePath X 1) ⁻¹' B) := by
    have hstart : ∀ᵐ ω ∂μ, X 0 ω = n + 1 :=
      blockedAtZeroInitialState_ae_eq_start (W := W) (P := P) (X := X) (n + 1)
    filter_upwards [hstart] with ω hω
    have hstart_out :
        X 0 ω ∉ insert (N + 2) ({0} : Set ℕ) := by
      simpa [hω] using hx
    have hτeq :
        hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0 ω =
          hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1 ω :=
      blockedAtZeroHittingAfter_zero_eq_one_of_not_mem_initial
        (W := W) (P := P) (X := X) hstart_out
    have hboundary : ({0, N + 2} : Set ℕ) = insert (N + 2) ({0} : Set ℕ) := by
      ext ξ
      simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_left_comm, or_comm]
    have htime :
        ({ω |
            hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1) ω = N + 2} ω) ↔
          ({ω |
            hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0 ω < ⊤ ∧
              stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω = N + 2} ω) := by
      have hstopEq :
          stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 0) ω =
            stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1) ω := by
        rw [stoppedValue, hτeq]
        rfl
      constructor
      · rintro ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq] using hfin
        · exact hstopEq.trans hstop
      · rintro ⟨hfin, hstop⟩
        refine ⟨?_, ?_⟩
        · simpa [hτeq] using hfin
        · exact hstopEq.symm.trans hstop
    -- Proof comment: away from the boundary, the time-`1` boundary-hit event is exactly the
    -- one-step future-path first-hit event.
    have hboundaryEq :
        (ω ∈
            {ω |
              hittingAfter X ({0, N + 2} : Set ℕ) 1 ω < ⊤ ∧
                stoppedValue X (hittingAfter X ({0, N + 2} : Set ℕ) 1) ω = N + 2}) ↔
          (ω ∈
            {ω |
              hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1 ω < ⊤ ∧
                stoppedValue X (hittingAfter X (insert (N + 2) ({0} : Set ℕ)) 1) ω = N + 2}) := by
      simpa [hboundary]
    exact
      propext <|
        hboundaryEq.trans <|
          htime.trans <|
            (blockedAtZeroFuturePath_mem_firstHitPathEvent_iff
              (u := X) ({0} : Set ℕ) (N + 2) hstart_out).symm
  calc
    F_A P X ({0} : Set ℕ) (n + 1) (N + 2)
        = μ.real ((natFuturePath X 1) ⁻¹' B) := by
            calc
              F_A P X ({0} : Set ℕ) (n + 1) (N + 2)
                  = μ.real
                      {ω |
                        hittingAfter X ({0, N + 2} : Set ℕ) 1 ω < ⊤ ∧
                          stoppedValue X (hittingAfter X ({0, N + 2} : Set ℕ) 1) ω = N + 2} := by
                            symm
                            simpa [μ, Measure.real_def] using
                              blockedAtZeroBoundaryHitDistribution_eq_F_A_of_not_mem_boundary
                                (W := W) (P := P) (X := X) (N := N) (x := n + 1) hx
              _ = μ.real ((natFuturePath X 1) ⁻¹' B) := by
                    exact MeasureTheory.measureReal_congr hEventAE
    _ = ∫ z,
          (blockedAtZeroRealizationPathKernel (P := P) (X := X) z).real B
            ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) (n + 1)) := by
              simpa [μ] using
                blockedAtZeroFuturePathHit_real_eq_pathKernelAverage
                  (W := W) (P := P) (X := X) B hB (n + 1)
    _ = ∫ z, F_A P X ({0} : Set ℕ) z (N + 2)
          ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) (n + 1)) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simpa [B] using
              (blockedAtZeroRealizationPathKernel_real_firstHitPathEvent_eq_F_A
                (W := W) (P := P) (X := X) ({0} : Set ℕ) (N + 2) z)

/-- Helper for Exercise 19.6.1: the blocked boundary row at `0` collapses to the right-jump branch
once the boundary datum vanishes at `0`. -/
private theorem blockedAtZeroBoundaryRowAverage_eq_rightJumpMul
    {W : HalfLineRandomEnvironment} {u : ℕ → ℝ} (hu0 : u 0 = 0) :
    ∫ z, u z ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0) =
      W.rightJumpProb 0 * u 1 := by
  let p : ℕ → ℕ → ℝ≥0∞ := blockedAtZeroRandomEnvironmentTransitionMatrix W
  let f : ℕ → ℝ := fun z ↦ (p 0 z).toReal * u z
  have hfinite01 : ({0, 1} : Set ℕ).Finite := by
    simpa [Set.insert_eq_of_mem] using (Set.finite_singleton 0).insert 1
  have hnorm_support :
      Function.support (fun z : ℕ ↦ (p 0 z).toReal * ‖u z‖) ⊆ ({0, 1} : Set ℕ) := by
    intro z hz
    by_cases hz0 : z = 0
    · simpa [hz0]
    · by_cases hz1 : z = 1
      · simpa [hz1]
      · have hpz : p 0 z = 0 := by
          simp [p, blockedAtZeroRandomEnvironmentTransitionMatrix, hz0, hz1]
        have : (p 0 z).toReal * ‖u z‖ = 0 := by simp [hpz]
        exact False.elim (hz <| by simpa [this])
  have hnorm :
      Summable (fun z : ℕ ↦ (p 0 z).toReal * ‖u z‖) :=
    summable_of_hasFiniteSupport (hfinite01.subset hnorm_support)
  have hu_tsum :
      ∫ z, u z ∂((discreteMatrixKernel p) 0) = ∑' z : ℕ, f z := by
    -- Proof comment: expand the boundary row integral into its explicit two-point series.
    simpa [f] using
      (integral_discreteMatrixKernel_eq_tsum p
        (blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic W) u 0 hnorm)
  have hsupport : ∀ z ∉ ({0, 1} : Finset ℕ), f z = 0 := by
    intro z hz
    have hz0 : z ≠ 0 := by
      intro h
      exact hz (by simp [h])
    have hz1 : z ≠ 1 := by
      intro h
      exact hz (by simp [h])
    simp [f, p, blockedAtZeroRandomEnvironmentTransitionMatrix, hz0, hz1]
  -- Proof comment: the blocked boundary row only sees the self-loop at `0` and the jump to `1`,
  -- and the self-loop term vanishes because `u 0 = 0`.
  rw [hu_tsum, tsum_eq_sum hsupport]
  simp [f, p, hu0, blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self,
    blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one]

/-- Helper for Exercise 19.6.1: the blocked half-line realization has the expected one-step joint
law for `(X n, X (n + 1))`. -/
private theorem blockedAtZeroMarkovRealization_transition
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (x n y z : ℕ) :
    (P x : Measure Ξ) {ω | X n ω = y ∧ X (n + 1) ω = z} =
      blockedAtZeroRandomEnvironmentTransitionMatrix W y z *
        (P x : Measure Ξ) (X n ⁻¹' ({y} : Set ℕ)) := by
  let μ : Measure Ξ := (P x : Measure Ξ)
  let A : Set Ξ := X n ⁻¹' {y}
  let B : Set Ξ := X (n + 1) ⁻¹' {z}
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X :=
    inferInstance
  have hA_meas : MeasurableSet A := by
    simpa [A] using (hReal.measurable_process n) (measurableSet_singleton y)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + 1)) (measurableSet_singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ξ› := by
    refine iSup₂_le fun m hm ↦ ?_
    exact (hReal.measurable_process m).comap_le
  have hA_measFiltration : MeasurableSet[generatedFiltrationSpace X n] A := by
    have hXn_measF : Measurable[generatedFiltrationSpace X n] (X n) := by
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le n <| le_iSup_of_le le_rfl le_rfl
    simpa [A] using hXn_measF (measurableSet_singleton y)
  have hEvent :
      {ω | X n ω = y ∧ X (n + 1) ω = z} = A ∩ B := by
    ext ω
    simp [A, B]
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦
          ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) (X n ω)).real
            ({z} : Set ℕ)) := by
    -- Proof comment: specialize the one-step Markov property to the singleton `{z}`.
    simpa [B, add_comm] using
      hReal.markov_property x (A := ({z} : Set ℕ)) (measurableSet_singleton z) n 1
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  have hInterReal :
      μ.real (A ∩ B) =
        (blockedAtZeroRandomEnvironmentTransitionMatrix W y z).toReal * μ.real A := by
    -- Proof comment: integrate the one-step conditional expectation over the fiber `X n = y`.
    calc
      μ.real (A ∩ B) = ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
        rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_measFiltration,
          ← integral_indicator hA_meas]
        symm
        simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
          smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_meas.inter hB_meas)
      _ =
          ∫ ω in A,
            ((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) (X n ω)).real
              ({z} : Set ℕ)) ∂ μ := by
            exact integral_congr_ae hMarkovGenerated.restrict
      _ = ∫ _ in A, (blockedAtZeroRandomEnvironmentTransitionMatrix W y z).toReal ∂ μ := by
            refine integral_congr_ae ?_
            filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_meas] with ω hω
            have hω : X n ω = y := by
              simpa [A] using hω
            rw [hω]
            rw [MeasureTheory.measureReal_def, discreteMatrixKernel_apply_singleton]
      _ = (blockedAtZeroRandomEnvironmentTransitionMatrix W y z).toReal * μ.real A := by
            rw [setIntegral_const, smul_eq_mul]
            rw [mul_comm]
  have hStep_ne_top : blockedAtZeroRandomEnvironmentTransitionMatrix W y z ≠ ∞ := by
    by_cases hy0 : y = 0
    · subst hy0
      by_cases hz0 : z = 0
      · simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hz0]
      · by_cases hz1 : z = 1
        · simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hz0, hz1]
        · simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hz0, hz1]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hy0
      by_cases hzLeft : z = k
      · simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hzLeft]
      · by_cases hzRight : z = k + 2
        · simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hzLeft, hzRight]
        · simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hzLeft, hzRight]
  have hInter :
      μ (A ∩ B) =
        blockedAtZeroRandomEnvironmentTransitionMatrix W y z * μ A := by
    refine
      (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ (A ∩ B))
        (ENNReal.mul_ne_top hStep_ne_top (measure_ne_top μ A))).mp ?_
    simpa [MeasureTheory.measureReal_def, ENNReal.toReal_mul, hStep_ne_top, A] using hInterReal
  -- Proof comment: rewrite the pair event as the intersection of current-state and next-state
  -- fibers, then transport the real-valued identity back to ENNReal.
  simpa [μ, A, hEvent] using hInter

/-- Helper for Exercise 19.6.1: from `0`, the blocked chain moves to either `0` or `1` after one
step almost surely. -/
private theorem blockedAtZeroOneStepBoundarySupport_ae
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X] :
    ∀ᵐ ω ∂(P 0 : Measure Ξ), X 1 ω = 0 ∨ X 1 ω = 1 := by
  let μ : Measure Ξ := (P 0 : Measure Ξ)
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X :=
    inferInstance
  let bad : Set Ξ := {ω | ¬ (X 1 ω = 0 ∨ X 1 ω = 1)}
  let badFiber : ℕ → Set Ξ := fun z ↦
    if z = 0 ∨ z = 1 then
      ∅
    else
      {ω | X 1 ω = z}
  have hbad_union : bad = ⋃ z : ℕ, badFiber z := by
    ext ω
    constructor
    · intro hω
      have hω0 : X 1 ω ≠ 0 := fun hEq ↦ hω (Or.inl hEq)
      have hω1' : X 1 ω ≠ 1 := fun hEq ↦ hω (Or.inr hEq)
      refine Set.mem_iUnion.2 ⟨X 1 ω, ?_⟩
      simp [badFiber, hω0, hω1']
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hz⟩
      by_cases hz01 : z = 0 ∨ z = 1
      · simp [badFiber, hz01] at hz
      · have hz' : X 1 ω = z := by
          simpa [badFiber, hz01] using hz
        have hz0 : z ≠ 0 := fun hEq ↦ hz01 (Or.inl hEq)
        have hz1 : z ≠ 1 := fun hEq ↦ hz01 (Or.inr hEq)
        simp [bad, hz', hz0, hz1]
  have hbad_zero : μ bad = 0 := by
    rw [hbad_union]
    have hbad_le_zero :
        μ (⋃ z : ℕ, badFiber z) ≤ 0 := by
      calc
        μ (⋃ z : ℕ, badFiber z) ≤ ∑' z : ℕ, μ (badFiber z) := by
              simpa using measure_iUnion_le (μ := μ) (s := badFiber)
        _ = ∑' z : ℕ, 0 := by
              refine tsum_congr ?_
              intro z
              by_cases hz01 : z = 0 ∨ z = 1
              · simp [badFiber, hz01]
              · have hStep :=
                  congrArg (fun ν : Measure ℕ ↦ ν ({z} : Set ℕ)) (hReal.transition_eq 0 1)
                have hStep' :
                    μ {ω | X 1 ω = z} =
                      blockedAtZeroRandomEnvironmentTransitionMatrix W 0 z := by
                  have hpreimage : {ω | X 1 ω = z} = X 1 ⁻¹' ({z} : Set ℕ) := by
                    ext ω
                    simp
                  rw [hpreimage]
                  rw [← Measure.map_apply (hReal.measurable_process 1) (measurableSet_singleton z)]
                  rw [hReal.transition_eq 0 1, pow_one, discreteMatrixKernel_apply_singleton]
                have hz0 : z ≠ 0 := fun hEq ↦ hz01 (Or.inl hEq)
                have hz1 : z ≠ 1 := fun hEq ↦ hz01 (Or.inr hEq)
                simpa [μ, badFiber, hz01, blockedAtZeroRandomEnvironmentTransitionMatrix, hz0, hz1]
                  using hStep'
        _ = 0 := by simp
    exact le_antisymm hbad_le_zero bot_le
  have hbad_ae : badᶜ ∈ ae μ := compl_mem_ae_iff.2 hbad_zero
  classical
  filter_upwards [hbad_ae] with ω hω
  have hω' : ¬¬ (X 1 ω = 0 ∨ X 1 ω = 1) := by
    simpa [bad] using hω
  exact not_not.mp hω'

/-- Helper for Exercise 19.6.1: once the blocked walk is at a positive state, the next step is
almost surely the left or right nearest neighbor. -/
private theorem blockedAtZeroPositiveStepSupport_ae
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (x : ℕ) :
    ∀ᵐ ω ∂(P x : Measure Ξ),
      ∀ n : ℕ, 0 < X n ω →
        X (n + 1) ω = X n ω - 1 ∨ X (n + 1) ω = X n ω + 1 := by
  let μ : Measure Ξ := (P x : Measure Ξ)
  let hReal :
      IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
        P X := inferInstance
  rw [ae_all_iff]
  intro n
  let bad : Set Ξ := {ω |
    0 < X n ω ∧
      ¬ (X (n + 1) ω = X n ω - 1 ∨ X (n + 1) ω = X n ω + 1)}
  let badFiber : ℕ → ℕ → Set Ξ := fun y z ↦
    if y = 0 ∨ z = y - 1 ∨ z = y + 1 then ∅ else {ω | X n ω = y ∧ X (n + 1) ω = z}
  have hbad_union :
      bad = ⋃ y : ℕ, ⋃ z : ℕ, badFiber y z := by
    ext ω
    constructor
    · rintro ⟨hpos, hω⟩
      have hy0 : X n ω ≠ 0 := Nat.ne_of_gt hpos
      have hzLeft : X (n + 1) ω ≠ X n ω - 1 := fun hEq ↦ hω (Or.inl hEq)
      have hzRight : X (n + 1) ω ≠ X n ω + 1 := fun hEq ↦ hω (Or.inr hEq)
      refine Set.mem_iUnion.2 ⟨X n ω, ?_⟩
      refine Set.mem_iUnion.2 ⟨X (n + 1) ω, ?_⟩
      simp [badFiber, hy0, hzLeft, hzRight]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨y, hy⟩
      rcases Set.mem_iUnion.1 hy with ⟨z, hz⟩
      by_cases hlegal : y = 0 ∨ z = y - 1 ∨ z = y + 1
      · simp [badFiber, hlegal] at hz
      · have hz' : X n ω = y ∧ X (n + 1) ω = z := by
          simpa [badFiber, hlegal] using hz
        have hy0 : y ≠ 0 := fun hEq ↦ hlegal (Or.inl hEq)
        have hzLeft : z ≠ y - 1 := fun hEq ↦ hlegal (Or.inr (Or.inl hEq))
        have hzRight : z ≠ y + 1 := fun hEq ↦ hlegal (Or.inr (Or.inr hEq))
        have hypos : 0 < y := Nat.pos_of_ne_zero hy0
        simp [bad, hz'.1, hz'.2, hypos, hzLeft, hzRight]
  have hbad_meas : MeasurableSet bad := by
    rw [hbad_union]
    refine MeasurableSet.iUnion fun y ↦ ?_
    refine MeasurableSet.iUnion fun z ↦ ?_
    by_cases hlegal : y = 0 ∨ z = y - 1 ∨ z = y + 1
    · simp [badFiber, hlegal]
    · have hXn : MeasurableSet {ω | X n ω = y} := by
        simpa [Set.preimage] using hReal.measurable_process n (measurableSet_singleton y)
      have hXsucc : MeasurableSet {ω | X (n + 1) ω = z} := by
        simpa [Set.preimage] using hReal.measurable_process (n + 1) (measurableSet_singleton z)
      have hpairMeas : MeasurableSet {ω | X n ω = y ∧ X (n + 1) ω = z} := by
        have hpairEq :
            {ω | X n ω = y ∧ X (n + 1) ω = z} =
              ({ω | X n ω = y} ∩ {ω | X (n + 1) ω = z}) := by
          ext ω
          simp
        rw [hpairEq]
        exact hXn.inter hXsucc
      simpa [badFiber, hlegal] using hpairMeas
  have hbad_zero : μ bad = 0 := by
    rw [hbad_union]
    have hbad_le_zero :
        μ (⋃ y : ℕ, ⋃ z : ℕ, badFiber y z) ≤ 0 := by
      calc
        μ (⋃ y : ℕ, ⋃ z : ℕ, badFiber y z)
            ≤ ∑' y : ℕ, μ (⋃ z : ℕ, badFiber y z) := by
                simpa using
                  measure_iUnion_le (μ := μ) (s := fun y : ℕ ↦ ⋃ z : ℕ, badFiber y z)
        _ ≤ ∑' y : ℕ, ∑' z : ℕ, μ (badFiber y z) := by
              refine ENNReal.tsum_le_tsum ?_
              intro y
              simpa using
                measure_iUnion_le (μ := μ) (s := fun z : ℕ ↦ badFiber y z)
        _ = ∑' y : ℕ, ∑' z : ℕ, 0 := by
              refine tsum_congr ?_
              intro y
              refine tsum_congr ?_
              intro z
              by_cases hlegal : y = 0 ∨ z = y - 1 ∨ z = y + 1
              · simp [badFiber, hlegal]
              · have hpair :
                    μ {ω | X n ω = y ∧ X (n + 1) ω = z} =
                      blockedAtZeroRandomEnvironmentTransitionMatrix W y z *
                        μ (X n ⁻¹' ({y} : Set ℕ)) := by
                    simpa [μ] using
                      blockedAtZeroMarkovRealization_transition
                        (W := W) (P := P) (X := X) x n y z
                have hmatrix : blockedAtZeroRandomEnvironmentTransitionMatrix W y z = 0 := by
                  have hy0 : y ≠ 0 := fun hEq ↦ hlegal (Or.inl hEq)
                  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hy0
                  have hzLeft : z ≠ k := fun hEq ↦ hlegal (Or.inr (Or.inl (by simpa [hEq])))
                  have hzRight : z ≠ k + 2 := fun hEq ↦
                    hlegal (Or.inr (Or.inr (by simpa [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm, hEq])))
                  simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hzLeft, hzRight]
                simpa [badFiber, hlegal, hpair, hmatrix]
        _ = 0 := by simp
    exact le_antisymm hbad_le_zero bot_le
  have hbad_ae : badᶜ ∈ ae μ := compl_mem_ae_iff.2 hbad_zero
  classical
  filter_upwards [hbad_ae] with ω hω
  intro hpos
  have hnot_bad :
      ¬ (0 < X n ω ∧
        ¬ (X (n + 1) ω = X n ω - 1 ∨ X (n + 1) ω = X n ω + 1)) := by
    simpa [bad] using hω
  by_contra hstep
  exact hnot_bad ⟨hpos, hstep⟩

/-- Helper for Exercise 19.6.1: for a path started at `1`, hitting the finite tail before `0`
means first hitting the boundary level `N + 2`. -/
private theorem blockedAtZeroFuturePath_mem_firstHitTail_iff
    (Y : ℕ → ℕ) (N : ℕ)
    (hstart : Y 0 = 1)
    (hstep : ∀ n : ℕ, 0 < Y n → Y (n + 1) = Y n - 1 ∨ Y (n + 1) = Y n + 1) :
    Y ∈ blockedAtZeroFirstHitPathEvent ({0} : Set ℕ) (N + 2) ↔
      ∃ n : ℕ, Y n ∈ Set.Ici (N + 2) ∧ ∀ m ≤ n, Y m ≠ 0 := by
  constructor
  · rintro ⟨n, hnHit, havoid⟩
    refine ⟨n, by simpa [hnHit], ?_⟩
    intro m hm
    by_cases hmn : m < n
    · exact fun hm0 ↦ havoid m hmn (by simp [hm0])
    · have hm_eq : m = n := le_antisymm hm (Nat.not_lt.mp hmn)
      simpa [hm_eq, hnHit]
  · rintro ⟨n, hnTail, hnozero⟩
    have hn_ge : N + 2 ≤ Y n := hnTail
    have hexists : ∃ m : ℕ, N + 2 ≤ Y m := ⟨n, hn_ge⟩
    let k : ℕ := Nat.find hexists
    have hk_ge : N + 2 ≤ Y k := Nat.find_spec hexists
    have hk_le : k ≤ n := Nat.find_min' hexists hn_ge
    have hk_pos : 0 < k := by
      by_contra hk0
      have hzero_lt : Y 0 < N + 2 := by simpa [hstart]
      have hk_zero : k = 0 := Nat.eq_zero_of_not_pos hk0
      exact not_lt_of_ge (hk_zero ▸ hk_ge) hzero_lt
    have hprev_lt : Y (k - 1) < N + 2 := by
      by_contra hprev_ge
      have hpred_le_n : k - 1 ≤ n := le_trans (Nat.pred_le _) hk_le
      have hk_le_pred : k ≤ k - 1 := by
        exact Nat.find_min' hexists (not_lt.mp hprev_ge)
      omega
    have hprev_pos : 0 < Y (k - 1) := by
      have hprev_ne_zero : Y (k - 1) ≠ 0 := hnozero (k - 1) (le_trans (Nat.pred_le _) hk_le)
      exact Nat.pos_of_ne_zero hprev_ne_zero
    have hpred_succ : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.succ_le_of_lt hk_pos)
    have hk_eq : Y k = N + 2 := by
      rcases hstep (k - 1) hprev_pos with hleft | hright
      · rw [hpred_succ] at hleft
        omega
      · rw [hpred_succ] at hright
        omega
    refine ⟨k, hk_eq, ?_⟩
    intro m hm
    have hm_ne_zero : Y m ≠ 0 := hnozero m (le_trans (Nat.le_of_lt hm) hk_le)
    have hm_lt_tail : Y m < N + 2 := by
      by_contra hm_ge
      have hk_le_m : k ≤ m := Nat.find_min' hexists (not_lt.mp hm_ge)
      exact not_lt_of_ge hk_le_m hm
    simp [hm_ne_zero, ne_of_lt hm_lt_tail]

/-- Helper for Exercise 19.6.1: a harmonic profile for the blocked half-line walk carries the
same conductance-weighted current across every interior edge. -/
private theorem blockedAtZeroHarmonicCurrent_eq
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) {u : ℕ → ℝ} {n : ℕ}
    (hu :
      u (n + 1) =
        ∫ z, u z ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
          (n + 1))) :
    (blockedAtZeroEdgeConductance W n).toReal * (u (n + 1) - u n) =
      (blockedAtZeroEdgeConductance W (n + 1)).toReal * (u (n + 2) - u (n + 1)) := by
  let p : ℕ → ℕ → ℝ≥0∞ := blockedAtZeroRandomEnvironmentTransitionMatrix W
  let f : ℕ → ℝ := fun z ↦ (p (n + 1) z).toReal * u z
  have hpair_finite : ({n, n + 2} : Set ℕ).Finite := by
    simpa [Set.insert_eq_of_mem] using (Set.finite_singleton n).insert (n + 2)
  have hnorm_support :
      Function.support (fun z : ℕ ↦ (p (n + 1) z).toReal * ‖u z‖) ⊆ ({n, n + 2} : Set ℕ) := by
    intro z hz
    by_cases hzLeft : z = n
    · simpa [hzLeft]
    · by_cases hzRight : z = n + 2
      · simpa [hzRight]
      · have hpz : p (n + 1) z = 0 := by
          simp [p, blockedAtZeroRandomEnvironmentTransitionMatrix_succ, hzLeft, hzRight]
        have : (p (n + 1) z).toReal * ‖u z‖ = 0 := by simp [hpz]
        exact False.elim (hz <| by simpa [this])
  have hnorm :
      Summable (fun z : ℕ ↦ (p (n + 1) z).toReal * ‖u z‖) :=
    summable_of_hasFiniteSupport (hpair_finite.subset hnorm_support)
  have hsupport : ∀ z ∉ ({n, n + 2} : Finset ℕ), f z = 0 := by
    intro z hz
    have hzLeft : z ≠ n := by
      intro h
      exact hz (by simp [h])
    have hzRight : z ≠ n + 2 := by
      intro h
      exact hz (by simp [h])
    simp [f, p, blockedAtZeroRandomEnvironmentTransitionMatrix_succ, hzLeft, hzRight]
  have hu_tsum : u (n + 1) = ∑' z : ℕ, f z := by
    -- Proof comment: rewrite the harmonicity assumption as the explicit two-neighbor row series.
    simpa [f] using
      (hu.trans <|
        integral_discreteMatrixKernel_eq_tsum p
          (blockedAtZeroRandomEnvironmentTransitionMatrix_isStochastic W) u (n + 1) hnorm)
  have hsplit :
      ∑' z : ℕ, f z = f n + f (n + 2) := by
    rw [tsum_eq_sum hsupport]
    simp [f]
  have hrow_ne_zero :
      conductance (blockedAtZeroConductance W) (n + 1) ≠ 0 :=
    ne_of_gt (blockedAtZeroConductance_vertexWeight_pos (W := W) hW (n + 1))
  have hrow_ne_top :
      conductance (blockedAtZeroConductance W) (n + 1) ≠ ∞ :=
    (blockedAtZeroConductance_vertexWeight_lt_top (W := W) hW (n + 1)).ne
  have hrow_toReal_ne_zero :
      (conductance (blockedAtZeroConductance W) (n + 1)).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hrow_ne_zero, hrow_ne_top⟩
  have hleftWeight :
      (p (n + 1) n).toReal =
        (blockedAtZeroEdgeConductance W n).toReal /
          (conductance (blockedAtZeroConductance W) (n + 1)).toReal := by
    simpa [p, conductanceTransitionMatrix_apply, blockedAtZeroConductance_backward,
      blockedAtZeroConductance_vertexWeight_succ, blockedAtZeroRandomEnvironmentTransitionMatrix_left,
      ENNReal.toReal_div, hrow_ne_zero, hrow_ne_top] using
      congrArg ENNReal.toReal
        (blockedAtZeroTransition_eq_conductanceTransitionMatrix (W := W) hW (n + 1) n)
  have hrightWeight :
      (p (n + 1) (n + 2)).toReal =
        (blockedAtZeroEdgeConductance W (n + 1)).toReal /
          (conductance (blockedAtZeroConductance W) (n + 1)).toReal := by
    simpa [p, conductanceTransitionMatrix_apply, blockedAtZeroConductance_forward,
      blockedAtZeroConductance_vertexWeight_succ, blockedAtZeroRandomEnvironmentTransitionMatrix_right,
      ENNReal.toReal_div, hrow_ne_zero, hrow_ne_top] using
      congrArg ENNReal.toReal
        (blockedAtZeroTransition_eq_conductanceTransitionMatrix (W := W) hW (n + 1) (n + 2))
  have hrow_toReal :
      (conductance (blockedAtZeroConductance W) (n + 1)).toReal =
        (blockedAtZeroEdgeConductance W n).toReal +
          (blockedAtZeroEdgeConductance W (n + 1)).toReal := by
    rw [blockedAtZeroConductance_vertexWeight_succ,
      ENNReal.toReal_add (blockedAtZeroEdgeConductance_ne_top hW n)
        (blockedAtZeroEdgeConductance_ne_top hW (n + 1))]
  have haverage :
      u (n + 1) =
        ((blockedAtZeroEdgeConductance W n).toReal /
            (conductance (blockedAtZeroConductance W) (n + 1)).toReal) * u n +
          ((blockedAtZeroEdgeConductance W (n + 1)).toReal /
            (conductance (blockedAtZeroConductance W) (n + 1)).toReal) * u (n + 2) := by
    calc
      u (n + 1) = ∑' z : ℕ, f z := hu_tsum
      _ = f n + f (n + 2) := hsplit
      _ =
          ((blockedAtZeroEdgeConductance W n).toReal /
              (conductance (blockedAtZeroConductance W) (n + 1)).toReal) * u n +
            ((blockedAtZeroEdgeConductance W (n + 1)).toReal /
              (conductance (blockedAtZeroConductance W) (n + 1)).toReal) * u (n + 2) := by
            simp [f, hleftWeight, hrightWeight]
  have hweighted :
      (conductance (blockedAtZeroConductance W) (n + 1)).toReal * u (n + 1) =
        (blockedAtZeroEdgeConductance W n).toReal * u n +
          (blockedAtZeroEdgeConductance W (n + 1)).toReal * u (n + 2) := by
    -- Proof comment: clear the common interior row denominator in the two-neighbor average.
    rw [haverage]
    field_simp [hrow_toReal_ne_zero]
  have hweighted' :
      ((blockedAtZeroEdgeConductance W n).toReal +
          (blockedAtZeroEdgeConductance W (n + 1)).toReal) * u (n + 1) =
        (blockedAtZeroEdgeConductance W n).toReal * u n +
          (blockedAtZeroEdgeConductance W (n + 1)).toReal * u (n + 2) := by
    simpa [hrow_toReal] using hweighted
  -- Proof comment: rearranging the weighted-average identity gives the conserved current across
  -- the two edges adjacent to `n + 1`.
  linarith

/-- Helper for Exercise 19.6.1: the remaining `succ` case factors the blocked escape event from
`0` through the deterministic first step to `1`, and the continuation law is exactly the first-hit
surface `F_A` on the finite boundary `{0, N + 2}`. -/
private theorem blockedAtZeroEscapeToTail_eq_rightJumpProb_mulFA
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (N : ℕ) :
    escapeToSetProbability P X 0 (Set.Ici (N + 2)) =
      W.rightJumpProb 0 * ENNReal.ofReal (F_A P X ({0} : Set ℕ) 1 (N + 2)) := by
  let μ : Measure Ξ := (P 0 : Measure Ξ)
  let B : Set (ℕ → ℕ) := blockedAtZeroFirstHitPathEvent ({0} : Set ℕ) (N + 2)
  let E : Set Ξ := {ω |
    ∃ n : ℕ, 0 < n ∧ X n ω ∈ Set.Ici (N + 2) ∧
      ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ 0}
  have hB : MeasurableSet B :=
    blockedAtZeroFirstHitPathEvent_measurable ({0} : Set ℕ) (N + 2)
  have hStepBoundary :
      ∀ᵐ ω ∂μ, X 1 ω = 0 ∨ X 1 ω = 1 :=
    blockedAtZeroOneStepBoundarySupport_ae (W := W) (P := P) (X := X)
  have hStepPositive :
      ∀ᵐ ω ∂μ, ∀ n : ℕ, 0 < X n ω →
        X (n + 1) ω = X n ω - 1 ∨ X (n + 1) ω = X n ω + 1 :=
    blockedAtZeroPositiveStepSupport_ae (W := W) (P := P) (X := X) 0
  have hEventAE :
      E =ᵐ[μ] ((natFuturePath X 1) ⁻¹' B) := by
    -- Route correction: instead of forcing the state-`0` future-path lemma, split on the a.e.
    -- boundary support `X 1 ∈ {0,1}` and use the positive nearest-neighbor support to turn a tail
    -- hit into the first hit of the exact boundary level `N + 2`.
    filter_upwards [hStepBoundary, hStepPositive] with ω hω1 hωStep
    apply propext
    constructor
    · intro hω
      rcases hω1 with hω1 | hω1
      · rcases hω with ⟨n, hn_pos, -, havoid⟩
        exact False.elim (havoid 1 (by simp) (Nat.succ_le_of_lt hn_pos) hω1)
      · have hTail :
            ∃ n : ℕ,
              natFuturePath X 1 ω n ∈ Set.Ici (N + 2) ∧
                ∀ m ≤ n, natFuturePath X 1 ω m ≠ 0 := by
          rcases hω with ⟨n, hn_pos, hnTail, havoid⟩
          refine ⟨n - 1, ?_, ?_⟩
          · have hpred_succ : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)
            simpa [natFuturePath, hpred_succ, Nat.add_comm] using hnTail
          · intro m hm
            have hm_le : m + 1 ≤ n := by omega
            simpa [natFuturePath, Nat.add_comm] using
              havoid (m + 1) (Nat.succ_pos _) hm_le
        have hFutureStep :
            ∀ n : ℕ,
              0 < natFuturePath X 1 ω n →
                natFuturePath X 1 ω (n + 1) = natFuturePath X 1 ω n - 1 ∨
                  natFuturePath X 1 ω (n + 1) = natFuturePath X 1 ω n + 1 := by
          intro n hn_pos
          simpa [natFuturePath, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hωStep (n + 1) hn_pos
        exact
          (blockedAtZeroFuturePath_mem_firstHitTail_iff
            (Y := natFuturePath X 1 ω) N hω1 hFutureStep).2 hTail
    · intro hω
      rcases hω1 with hω1 | hω1
      · have : natFuturePath X 1 ω ∉ B := by
          intro hBω
          rcases hBω with ⟨n, hnHit, havoid⟩
          cases n with
          | zero =>
              simp [B, blockedAtZeroFirstHitPathEvent, natFuturePath, hω1] at hnHit
          | succ n =>
              have hzero :
                  natFuturePath X 1 ω 0 ∉ insert (N + 2) ({0} : Set ℕ) := havoid 0 (Nat.zero_lt_succ n)
              simp [natFuturePath, hω1] at hzero
        exact False.elim (this hω)
      · have hFutureStep :
            ∀ n : ℕ,
              0 < natFuturePath X 1 ω n →
                natFuturePath X 1 ω (n + 1) = natFuturePath X 1 ω n - 1 ∨
                  natFuturePath X 1 ω (n + 1) = natFuturePath X 1 ω n + 1 := by
          intro n hn_pos
          simpa [natFuturePath, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hωStep (n + 1) hn_pos
        rcases
            (blockedAtZeroFuturePath_mem_firstHitTail_iff
              (Y := natFuturePath X 1 ω) N hω1 hFutureStep).1 hω with
          ⟨n, hnTail, hnozero⟩
        refine ⟨n + 1, Nat.succ_pos _, ?_, ?_⟩
        · simpa [natFuturePath, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnTail
        · intro m hm_pos hm_le
          obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
          have hk_le : k ≤ n := Nat.succ_le_succ_iff.mp hm_le
          simpa [natFuturePath, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            hnozero k hk_le
  have hFutureReal :
      μ.real ((natFuturePath X 1) ⁻¹' B) =
        ∫ z, F_A P X ({0} : Set ℕ) z (N + 2)
          ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0) := by
    calc
      μ.real ((natFuturePath X 1) ⁻¹' B)
          = ∫ z,
              (blockedAtZeroRealizationPathKernel (P := P) (X := X) z).real B
                ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0) := by
              simpa [μ] using
                blockedAtZeroFuturePathHit_real_eq_pathKernelAverage
                  (W := W) (P := P) (X := X) B hB 0
      _ = ∫ z, F_A P X ({0} : Set ℕ) z (N + 2)
            ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simpa [B] using
              (blockedAtZeroRealizationPathKernel_real_firstHitPathEvent_eq_F_A
                (W := W) (P := P) (X := X) ({0} : Set ℕ) (N + 2) z)
  have hu0 : F_A P X ({0} : Set ℕ) 0 (N + 2) = 0 := by
    -- Proof comment: the boundary point `0` already carries the left Dirichlet datum.
    simpa using
      blockedAtZeroFA_eq_boundaryDatum_on_boundary
        (W := W) (P := P) (X := X) N 0 (by simp)
  have hCollapse :
      ∫ z, F_A P X ({0} : Set ℕ) z (N + 2)
          ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0) =
        W.rightJumpProb 0 * F_A P X ({0} : Set ℕ) 1 (N + 2) := by
    -- Proof comment: on the boundary row at `0`, only the self-loop and the jump to `1`
    -- contribute, and the self-loop term vanishes because `F_A(0) = 0`.
    simpa using
      blockedAtZeroBoundaryRowAverage_eq_rightJumpMul
        (W := W) (u := fun z ↦ F_A P X ({0} : Set ℕ) z (N + 2)) hu0
  calc
    escapeToSetProbability P X 0 (Set.Ici (N + 2)) = μ E := by
        simpa [μ, E] using escapeToSetProbability_def P X 0 (Set.Ici (N + 2))
    _ = ENNReal.ofReal (μ.real ((natFuturePath X 1) ⁻¹' B)) := by
          rw [measure_congr hEventAE]
          simp [Measure.real_def]
    _ =
        ENNReal.ofReal
          (∫ z, F_A P X ({0} : Set ℕ) z (N + 2)
            ∂((discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) 0)) := by
              rw [hFutureReal]
    _ = ENNReal.ofReal (W.rightJumpProb 0 * F_A P X ({0} : Set ℕ) 1 (N + 2)) := by
          rw [hCollapse]
    _ = W.rightJumpProb 0 * ENNReal.ofReal (F_A P X ({0} : Set ℕ) 1 (N + 2)) := by
          rw [ENNReal.ofReal_mul (show 0 ≤ (W.rightJumpProb 0 : ℝ) by positivity)]
          simp

/-- Helper for Exercise 19.6.1: prefix sums of successive drops telescope to the endpoint
voltage difference. -/
private theorem blockedAtZeroPrefixDrops_telescope (u : ℕ → ℝ) (k : ℕ) :
    Finset.sum (Finset.range k) (fun i ↦ (u (i + 1) - u i)) = u k - u 0 := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Proof comment: split off the last edge drop and telescope the remaining prefix by the
      -- induction hypothesis.
      rw [Finset.sum_range_succ, ih]
      ring

/-- Helper for Exercise 19.6.1: on each interior prefix edge, the blocked first-hit voltage has
constant conductance flux. -/
private theorem blockedAtZeroVoltageFlux_step
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) {N n : ℕ} (hn : n ≤ N) :
    (blockedAtZeroEdgeConductance W n).toReal *
        (F_A P X ({0} : Set ℕ) (n + 1) (N + 2) - F_A P X ({0} : Set ℕ) n (N + 2)) =
      (blockedAtZeroEdgeConductance W (n + 1)).toReal *
        (F_A P X ({0} : Set ℕ) (n + 2) (N + 2) - F_A P X ({0} : Set ℕ) (n + 1) (N + 2)) := by
  -- Route correction: consume the new blocked-half-line current lemma instead of repeating the
  -- two-neighbor row normalization inside the voltage proof.
  exact
    blockedAtZeroHarmonicCurrent_eq (W := W) hW (n := n)
      (u := fun k ↦ F_A P X ({0} : Set ℕ) k (N + 2))
      (by simpa using blockedAtZeroFA_average_eq_interior (W := W) (P := P) (X := X) hn)

/-- Helper for Exercise 19.6.1: every prefix edge carries the same conductance-weighted current as
the boundary edge `{0,1}`. -/
private theorem blockedAtZeroVoltageFlux_eq_boundaryCurrent
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) (N i : ℕ) (hi : i ≤ N + 1) :
    (blockedAtZeroEdgeConductance W i).toReal *
        (F_A P X ({0} : Set ℕ) (i + 1) (N + 2) - F_A P X ({0} : Set ℕ) i (N + 2)) =
      (blockedAtZeroEdgeConductance W 0).toReal * F_A P X ({0} : Set ℕ) 1 (N + 2) := by
  let u : ℕ → ℝ := fun k ↦ F_A P X ({0} : Set ℕ) k (N + 2)
  induction i generalizing N with
  | zero =>
      have hu0 : u 0 = 0 := by
        simpa [u] using
          blockedAtZeroFA_eq_boundaryDatum_on_boundary
            (W := W) (P := P) (X := X) N 0 (by simp)
      -- Proof comment: at the left boundary, the common current is exactly the edge-`0` drop
      -- because the boundary datum vanishes at `0`.
      simpa [u, hu0]
  | succ i ih =>
      have hiN : i ≤ N := by
        omega
      have hprev := ih N (by omega : i ≤ N + 1)
      have hstep :=
        blockedAtZeroVoltageFlux_step (W := W) (P := P) (X := X) hW (N := N) (n := i) hiN
      -- Proof comment: propagate the boundary current one edge to the right by the interior
      -- current-conservation step.
      exact hstep.symm.trans hprev

/-- Helper for Exercise 19.6.1: the continuation value at state `1` is the reciprocal blocked
prefix resistance scaled by the boundary conductance `blockedAtZeroEdgeConductance W 0`. -/
private theorem blockedAtZeroFA_one_eq_prefixResistanceRatio
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) (N : ℕ) :
    ENNReal.ofReal (F_A P X ({0} : Set ℕ) 1 (N + 2)) =
      (blockedAtZeroEdgeConductance W 0)⁻¹ *
        ((Finset.sum (Finset.range (N + 2))
          fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹) := by
  let u : ℕ → ℝ := fun k ↦ F_A P X ({0} : Set ℕ) k (N + 2)
  let s : ℝ := Finset.sum (Finset.range (N + 2)) fun i ↦
    ((blockedAtZeroEdgeConductance W i)⁻¹).toReal
  have hu0 : u 0 = 0 := by
    simpa [u] using
      blockedAtZeroFA_eq_boundaryDatum_on_boundary
        (W := W) (P := P) (X := X) N 0 (by simp)
  have huBoundary : u (N + 2) = 1 := by
    simpa [u] using
      blockedAtZeroFA_eq_boundaryDatum_on_boundary
        (W := W) (P := P) (X := X) N (N + 2) (by simp)
  have hstep :
      ∀ i ∈ Finset.range (N + 2),
        u (i + 1) - u i =
          ((blockedAtZeroEdgeConductance W 0).toReal * u 1) *
            ((blockedAtZeroEdgeConductance W i)⁻¹).toReal := by
    intro i hi
    have hi_le : i ≤ N + 1 := by
      exact Nat.lt_succ_iff.mp (by simpa [Nat.add_assoc] using Finset.mem_range.mp hi)
    have hflux :=
      blockedAtZeroVoltageFlux_eq_boundaryCurrent
        (W := W) (P := P) (X := X) hW N i hi_le
    have hci_ne_zero : (blockedAtZeroEdgeConductance W i).toReal ≠ 0 := by
      exact ENNReal.toReal_ne_zero.mpr
        ⟨(blockedAtZeroEdgeConductance_pos hW i).ne',
          blockedAtZeroEdgeConductance_ne_top hW i⟩
    have hdiff :
        u (i + 1) - u i =
          ((blockedAtZeroEdgeConductance W 0).toReal * u 1) /
            (blockedAtZeroEdgeConductance W i).toReal := by
      apply (eq_div_iff hci_ne_zero).2
      simpa [u, mul_assoc, mul_left_comm, mul_comm] using hflux
    calc
      u (i + 1) - u i
          = ((blockedAtZeroEdgeConductance W 0).toReal * u 1) /
              (blockedAtZeroEdgeConductance W i).toReal := hdiff
      _ = ((blockedAtZeroEdgeConductance W 0).toReal * u 1) *
            ((blockedAtZeroEdgeConductance W i)⁻¹).toReal := by
            rw [div_eq_mul_inv, ENNReal.toReal_inv]
  have hsumCurrent :
      ((blockedAtZeroEdgeConductance W 0).toReal * u 1) * s = 1 := by
    calc
      ((blockedAtZeroEdgeConductance W 0).toReal * u 1) * s
          = Finset.sum (Finset.range (N + 2)) (fun i ↦
              ((blockedAtZeroEdgeConductance W 0).toReal * u 1) *
                ((blockedAtZeroEdgeConductance W i)⁻¹).toReal) := by
                simp [s, Finset.mul_sum]
      _ = Finset.sum (Finset.range (N + 2)) (fun i ↦ u (i + 1) - u i) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            symm
            exact hstep i hi
      _ = u (N + 2) - u 0 := blockedAtZeroPrefixDrops_telescope u (N + 2)
      _ = 1 := by simp [hu0, huBoundary]
  have hc0s_ne_zero :
      (blockedAtZeroEdgeConductance W 0).toReal * s ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact ENNReal.toReal_ne_zero.mpr
        ⟨(blockedAtZeroEdgeConductance_pos hW 0).ne',
          blockedAtZeroEdgeConductance_ne_top hW 0⟩
    · have hs_pos : 0 < s := by
        have hterm_pos : 0 < ((blockedAtZeroEdgeConductance W 0)⁻¹).toReal := by
          exact ENNReal.toReal_pos
            (by simpa using inv_ne_zero (show blockedAtZeroEdgeConductance W 0 ≠ 0 from
              (blockedAtZeroEdgeConductance_pos hW 0).ne'))
            (by simpa using ENNReal.inv_ne_top.2 ((blockedAtZeroEdgeConductance_pos hW 0).ne'))
        have hterm_le :
            ((blockedAtZeroEdgeConductance W 0)⁻¹).toReal ≤ s := by
          have hzero_mem : 0 ∈ Finset.range (N + 2) := by simp
          simpa [s] using
            (Finset.single_le_sum
              (s := Finset.range (N + 2))
              (f := fun i ↦ ((blockedAtZeroEdgeConductance W i)⁻¹).toReal)
              (a := 0)
              (fun i _ ↦ by positivity) hzero_mem :
              ((blockedAtZeroEdgeConductance W 0)⁻¹).toReal ≤
                Finset.sum (Finset.range (N + 2)) fun i ↦
                  ((blockedAtZeroEdgeConductance W i)⁻¹).toReal)
        exact lt_of_lt_of_le hterm_pos hterm_le
      exact hs_pos.ne'
  have hu1_real :
      u 1 =
        ((blockedAtZeroEdgeConductance W 0).toReal)⁻¹ * s⁻¹ := by
    have hcurrent' :
        u 1 * ((blockedAtZeroEdgeConductance W 0).toReal * s) = 1 := by
      simpa [s, mul_assoc, mul_left_comm, mul_comm] using hsumCurrent
    have hcurrent'' :
        ((blockedAtZeroEdgeConductance W 0).toReal * s) * u 1 = 1 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hcurrent'
    have hu1_inv :
        u 1 = ((blockedAtZeroEdgeConductance W 0).toReal * s)⁻¹ := by
      exact (inv_eq_of_mul_eq_one_right hcurrent'').symm
    calc
      u 1 = ((blockedAtZeroEdgeConductance W 0).toReal * s)⁻¹ := hu1_inv
      _ = ((blockedAtZeroEdgeConductance W 0).toReal)⁻¹ * s⁻¹ := by
            rw [mul_inv_rev, mul_comm]
  have hsum_toReal :
      (Finset.sum (Finset.range (N + 2)) fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹).toReal = s := by
    rw [ENNReal.toReal_sum]
    · intro i hi
      simpa using ENNReal.inv_ne_top.2 ((blockedAtZeroEdgeConductance_pos hW i).ne')
  have hsum_ne_zero :
      Finset.sum (Finset.range (N + 2)) (fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹) ≠ 0 := by
    have hsum_pos :
        0 < Finset.sum (Finset.range (N + 2)) fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹ := by
      have hterm_pos : 0 < (blockedAtZeroEdgeConductance W 0)⁻¹ := by
        simpa using
          ENNReal.inv_pos.mpr (show 0 < blockedAtZeroEdgeConductance W 0 from
            blockedAtZeroEdgeConductance_pos hW 0)
      have hzero_mem : 0 ∈ Finset.range (N + 2) := by simp
      have hterm_le :
          (blockedAtZeroEdgeConductance W 0)⁻¹ ≤
            Finset.sum (Finset.range (N + 2)) fun i ↦
              (blockedAtZeroEdgeConductance W i)⁻¹ := by
        exact Finset.single_le_sum
          (s := Finset.range (N + 2))
          (f := fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)
          (a := 0)
          (fun i _ ↦ by exact zero_le _)
          hzero_mem
      exact lt_of_lt_of_le hterm_pos hterm_le
    exact hsum_pos.ne'
  have hrhs_ne_top :
      (blockedAtZeroEdgeConductance W 0)⁻¹ *
          ((Finset.sum (Finset.range (N + 2))
            fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹) ≠ ∞ := by
    refine ENNReal.mul_ne_top ?_ ?_
    · simpa using ENNReal.inv_ne_top.2 ((blockedAtZeroEdgeConductance_pos hW 0).ne')
    · simpa using ENNReal.inv_ne_top.2 hsum_ne_zero
  apply (ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top hrhs_ne_top).1
  calc
    (ENNReal.ofReal (F_A P X ({0} : Set ℕ) 1 (N + 2))).toReal
        = u 1 := by
            have hFA_nonneg : 0 ≤ F_A P X ({0} : Set ℕ) 1 (N + 2) := by
              rw [F_A]
              exact ENNReal.toReal_nonneg
            rw [ENNReal.toReal_ofReal hFA_nonneg]
    _ = ((blockedAtZeroEdgeConductance W 0).toReal)⁻¹ * s⁻¹ := hu1_real
    _ =
        ((blockedAtZeroEdgeConductance W 0)⁻¹ *
          ((Finset.sum (Finset.range (N + 2))
            fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹)).toReal := by
              rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, hsum_toReal]

/-- Helper for Exercise 19.6.1: the boundary conductance normalization cancels the first-step
right-jump factor at `0`. -/
private theorem blockedAtZeroRightJumpProb_mul_invBoundaryConductance
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) :
    W.rightJumpProb 0 * (blockedAtZeroEdgeConductance W 0)⁻¹ = 1 := by
  have hp0_ne_zero : (W.rightJumpProb 0 : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (hW.pos 0).ne'
  -- Proof comment: the boundary conductance is exactly `W.rightJumpProb 0`, so the product is a
  -- direct inverse cancellation in `ℝ≥0∞`.
  rw [blockedAtZeroEdgeConductance_zero, ENNReal.mul_inv_cancel hp0_ne_zero (by simp)]

/-- Helper for Exercise 19.6.1: escaping from `0` to `Set.Ici 1` is exactly the event that the
first step lands at `1`, because the blocked boundary row only has the support `{0,1}`. -/
private theorem blockedAtZeroEscapeToIci_one_eq_rightJumpProb
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X] :
    escapeToSetProbability P X 0 (Set.Ici 1) = W.rightJumpProb 0 := by
  let μ : Measure Ξ := (P 0 : Measure Ξ)
  have hEventAE :
      {ω |
          ∃ n : ℕ,
            0 < n ∧ X n ω ∈ Set.Ici 1 ∧
              ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ 0} =ᵐ[μ]
        {ω | X 1 ω = 1} := by
    have hsupport :=
      blockedAtZeroOneStepBoundarySupport_ae (W := W) (P := P) (X := X)
    filter_upwards [hsupport] with ω hω
    apply propext
    constructor
    · rintro ⟨n, hn_pos, -, hnoReturn⟩
      have h1_ne_zero : X 1 ω ≠ 0 :=
        hnoReturn 1 (by simp) (by omega)
      rcases hω with h10 | h11
      · exact False.elim (h1_ne_zero h10)
      · exact h11
    · intro h1
      have h1_eq : X 1 ω = 1 := h1
      refine ⟨1, by simp, ?_, ?_⟩
      · simpa [Set.mem_Ici] using (show 1 ≤ X 1 ω from le_of_eq h1_eq.symm)
      · intro m hm_pos hm_le
        have hm1 : m = 1 := by omega
        have h1_ne_zero : X 1 ω ≠ 0 := by simpa [h1_eq]
        simpa [hm1] using h1_ne_zero
  -- Proof comment: at the blocked boundary, escaping to `Set.Ici 1` is equivalent to taking the
  -- unique non-self-loop branch at the first step.
  calc
    escapeToSetProbability P X 0 (Set.Ici 1) =
        μ {ω |
          ∃ n : ℕ,
            0 < n ∧ X n ω ∈ Set.Ici 1 ∧
              ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ 0} := by
          rw [escapeToSetProbability_def]
    _ = μ {ω | X 1 ω = 1} := by
          rw [measure_congr hEventAE]
    _ = W.rightJumpProb 0 :=
      blockedAtZeroOneStep_one_prob_eq_rightJumpProb (W := W) (P := P) (X := X)

/-- Helper for Exercise 19.6.1: the escape probability from `0` to the finite tail
`Set.Ici (N + 1)` is the reciprocal of the blocked prefix-resistance sum through edge `N`. -/
theorem blockedAtZeroEscapeToIci_eq_invPrefixResistance
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) (N : ℕ) :
    escapeToSetProbability P X 0 (Set.Ici (N + 1)) =
      (Finset.sum (Finset.range (N + 1))
        fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹ := by
  cases N with
  | zero =>
      -- Proof comment: for the first tail `Set.Ici 1`, the escape event is just the one-step jump
      -- to `1`, and the prefix resistance has one boundary edge.
      simpa using
        (blockedAtZeroEscapeToIci_one_eq_rightJumpProb (W := W) (P := P) (X := X)).trans
          (blockedAtZeroInvPrefixResistance_zero (W := W) hW).symm
  | succ N =>
      -- Proof comment: for larger finite tails, factor the escape event through the first jump to
      -- `1`, then substitute the finite-prefix `F_A(1)` resistance formula.
      calc
        escapeToSetProbability P X 0 (Set.Ici (N + 2)) =
            W.rightJumpProb 0 * ENNReal.ofReal (F_A P X ({0} : Set ℕ) 1 (N + 2)) := by
              exact blockedAtZeroEscapeToTail_eq_rightJumpProb_mulFA (W := W) (P := P) (X := X) N
        _ = W.rightJumpProb 0 *
              ((blockedAtZeroEdgeConductance W 0)⁻¹ *
                ((Finset.sum (Finset.range (N + 2))
                  fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹)) := by
                rw [blockedAtZeroFA_one_eq_prefixResistanceRatio (W := W) (P := P) (X := X) hW N]
        _ = (W.rightJumpProb 0 * (blockedAtZeroEdgeConductance W 0)⁻¹) *
              ((Finset.sum (Finset.range (N + 2))
                fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹) := by
                rw [mul_assoc]
        _ = 1 *
              ((Finset.sum (Finset.range (N + 2))
                fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹) := by
                rw [blockedAtZeroRightJumpProb_mul_invBoundaryConductance hW]
        _ = (Finset.sum (Finset.range (N + 2))
              fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹ := by simp

/-- Helper for Exercise 19.6.1: the cofinite exhaustion `Set.Ici (N + 1)` computes the blocked
effective conductance to infinity as the infimum of the corresponding escape-to-set
probabilities. -/
theorem blockedAtZeroEffectiveConductanceToInfinity_eq_iInf_escapeToIci
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X] :
    effectiveConductanceToInfinity (blockedAtZeroConductance W) P X 0 =
      ⨅ N : ℕ, escapeToSetProbability P X 0 (Set.Ici (N + 1)) := by
  let A : ℕ → Set ℕ := fun N ↦ Set.Ici (N + 1)
  have hA :
      Set.DecreasesTo A (∅ : Set ℕ) := by
    refine ⟨?_, ?_⟩
    · intro m n hmn
      exact Set.Ici_subset_Ici.2 (Nat.succ_le_succ hmn)
    · ext x
      constructor
      · intro hx
        have hx' : x + 1 ≤ x := by
          exact Set.mem_iInter.mp hx x
        exact False.elim (Nat.not_succ_le_self x hx')
      · intro hx
        simp at hx
  have hfinite : ∀ N : ℕ, (A N)ᶜ.Finite := by
    intro N
    simpa [A, Set.compl_setOf, Nat.not_le] using (Set.finite_Iic N)
  have hzero : ∀ N : ℕ, 0 ∉ A N := by
    intro N
    simp [A]
  have hlimit_eff :
      Tendsto (fun N ↦ escapeToSetProbability P X 0 (A N)) atTop
        (nhds (effectiveConductanceToInfinity (blockedAtZeroConductance W) P X 0)) := by
    -- Proof comment: at the boundary state `0`, the conductance prefactor from Lemma 19.24 is
    -- exactly `1`, so the finite-boundary conductance terms are the bare escape probabilities.
    simpa [A, blockedAtZeroConductance_vertexWeight_zero] using
      effectiveConductanceToInfinity_tendsto_of_decreasing_finite_complement
        (C := blockedAtZeroConductance W) (P := P) (X := X) (x₁ := 0)
        hA hfinite hzero (by simpa [blockedAtZeroConductance_vertexWeight_zero])
  have hanti :
      Antitone (fun N ↦ escapeToSetProbability P X 0 (A N)) := by
    intro m n hmn
    exact escapeToSetProbability_mono P X 0 (hA.antitone hmn)
  have hlimit_iInf :
      Tendsto (fun N ↦ escapeToSetProbability P X 0 (A N)) atTop
        (nhds (⨅ N : ℕ, escapeToSetProbability P X 0 (A N))) :=
    tendsto_atTop_iInf hanti
  -- Proof comment: the decreasing exhaustion has a unique limit, so the `iInf` normal form is
  -- exactly the effective conductance to infinity.
  exact tendsto_nhds_unique hlimit_eff hlimit_iInf

/-- Helper for Exercise 19.6.1: the reciprocal prefix-resistance infimum vanishes exactly when
the full blocked resistance series diverges. -/
theorem blockedAtZeroInvPrefixResistance_iInf_eq_zero_iff_resistanceSeries
    (W : HalfLineRandomEnvironment) :
    (⨅ N : ℕ,
        (Finset.sum (Finset.range (N + 1))
          fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹) = 0 ↔
      (∑' n, (blockedAtZeroEdgeConductance W n)⁻¹) = ∞ := by
  let f : ℕ → ℝ≥0∞ := fun n ↦ (blockedAtZeroEdgeConductance W n)⁻¹
  have hsup :
      (⨆ N : ℕ, Finset.sum (Finset.range (N + 1)) fun i ↦ f i) = ∑' n, f n := by
    simpa [f] using
      (ENNReal.tsum_eq_iSup_nat' (f := f) (N := fun n ↦ n + 1)
        (by simpa using tendsto_add_atTop_nat 1)).symm
  -- Proof comment: the infimum of the reciprocal prefix sums is the reciprocal of the supremum of
  -- the prefix sums, and for `ℝ≥0∞` that reciprocal is zero exactly at `∞`.
  rw [← ENNReal.inv_iSup (fun N : ℕ ↦ Finset.sum (Finset.range (N + 1)) fun i ↦ f i),
    ENNReal.inv_eq_zero,
    hsup]

/-- Helper for Exercise 19.6.1: after the finite-tail escape identity is available, vanishing
effective conductance is equivalent to divergence of the blocked resistance series. -/
theorem blockedAtZeroEffectiveConductanceToInfinity_eq_zero_iff_resistanceSeries
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) :
    effectiveConductanceToInfinity (blockedAtZeroConductance W) P X 0 = 0 ↔
      (∑' n, (blockedAtZeroEdgeConductance W n)⁻¹) = ∞ := by
  rw [blockedAtZeroEffectiveConductanceToInfinity_eq_iInf_escapeToIci (P := P) (X := X) (W := W)]
  have hrewrite :
      (fun N : ℕ ↦ escapeToSetProbability P X 0 (Set.Ici (N + 1))) =
        fun N : ℕ ↦
          (Finset.sum (Finset.range (N + 1))
            fun i ↦ (blockedAtZeroEdgeConductance W i)⁻¹)⁻¹ := by
    funext N
    exact blockedAtZeroEscapeToIci_eq_invPrefixResistance
      (P := P) (X := X) (W := W) hW N
  rw [hrewrite]
  exact blockedAtZeroInvPrefixResistance_iInf_eq_zero_iff_resistanceSeries W

/-- Helper for Exercise 19.6.1: the blocked half-line chain is recurrent at `0` exactly when the
reciprocal blocked conductance series diverges. -/
theorem blockedAtZeroStateZeroRecurrent_iff_resistanceSeries
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) :
    IsRecurrentState P X 0 ↔
      (∑' n, (blockedAtZeroEdgeConductance W n)⁻¹) = ∞ := by
  rw [blockedAtZeroStateZeroRecurrent_iff_effectiveResistanceToInfinity_eq_top
    (P := P) (X := X) (W := W) hW]
  rw [← effectiveConductanceToInfinity_eq_zero_iff_effectiveResistanceToInfinity_eq_top
    (C := blockedAtZeroConductance W) (P := P) (X := X) (x₁ := 0)]
  -- Proof comment: after reducing recurrence to vanishing effective conductance, the only
  -- remaining input is the finite-tail escape formula isolated above.
  exact blockedAtZeroEffectiveConductanceToInfinity_eq_zero_iff_resistanceSeries
    (P := P) (X := X) (W := W) hW

/-- Helper for Exercise 19.6.1: finite total conductance mass normalizes the reversible
conductance measure to an invariant distribution charging `0`, so the boundary state is positive
recurrent. -/
private theorem blockedAtZeroStateZeroPositiveRecurrent_of_conductanceSeries_lt_top
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic)
    (hseries : (∑' n, blockedAtZeroEdgeConductance W n) < ∞) :
    IsPositiveRecurrentState P X 0 := by
  let μC : Measure ℕ := conductanceMeasure (blockedAtZeroConductance W)
  have hmass_lt_top : μC Set.univ < ∞ :=
    blockedAtZeroConductanceMeasure_univ_lt_top_of_series_lt_top W hseries
  have hmass_ne_zero : μC Set.univ ≠ 0 := by
    intro hzero
    have hsingleton : μC ({0} : Set ℕ) = 0 := by
      simpa [μC] using
        (measure_mono_null (show ({0} : Set ℕ) ⊆ Set.univ by simp) hzero)
    -- Proof comment: the conductance measure already assigns mass `1` to the boundary singleton.
    simpa [μC, conductanceMeasure_apply_singleton, blockedAtZeroConductance_vertexWeight_zero] using
      hsingleton
  let πMeasure : Measure ℕ := (μC Set.univ)⁻¹ • μC
  have hπ_prob : IsProbabilityMeasure πMeasure := by
    refine isProbabilityMeasure_iff.2 ?_
    rw [Measure.smul_apply]
    exact ENNReal.inv_mul_cancel hmass_ne_zero (ne_of_lt hmass_lt_top)
  let π : ProbabilityMeasure ℕ := ⟨πMeasure, hπ_prob⟩
  have hμC_inv_conductance :
      Kernel.Invariant
        (discreteMatrixKernel (conductanceTransitionMatrix (blockedAtZeroConductance W)))
        μC := by
    letI :
        IsMarkovKernel
          (discreteMatrixKernel (conductanceTransitionMatrix (blockedAtZeroConductance W))) :=
      discreteMatrixKernel_isMarkovKernel _
        (conductanceTransitionMatrix_isStochastic
          (C := blockedAtZeroConductance W)
          (blockedAtZeroConductance_vertexWeight_lt_top hW)
          (blockedAtZeroConductance_vertexWeight_pos hW))
    -- Proof comment: reversibility of the conductance presentation supplies the raw invariant
    -- measure before normalization.
    exact
      (conductanceKernel_isReversible
        (C := blockedAtZeroConductance W)
        (blockedAtZeroConductance_symmetric W)
        (blockedAtZeroConductance_vertexWeight_lt_top hW)
        (blockedAtZeroConductance_vertexWeight_pos hW)).invariant
  have hp_eq :
      blockedAtZeroRandomEnvironmentTransitionMatrix W =
        conductanceTransitionMatrix (blockedAtZeroConductance W) := by
    funext x y
    exact blockedAtZeroTransition_eq_conductanceTransitionMatrix hW x y
  have hμC_inv :
      Kernel.Invariant
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
        μC := by
    simpa [μC, hp_eq] using hμC_inv_conductance
  have hπ_inv :
      Kernel.Invariant
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
        (π : Measure ℕ) := by
    simpa [π, πMeasure] using
      (kernelInvariant_smul
        (κ := fun _ : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
        (a := (μC Set.univ)⁻¹) hμC_inv)
  have hπ0_pos : 0 < (π : Measure ℕ) ({0} : Set ℕ) := by
    have hμC0_pos : 0 < μC ({0} : Set ℕ) := by
      -- Proof comment: the boundary singleton has raw conductance mass `1`.
      simpa [μC, conductanceMeasure_apply_singleton, blockedAtZeroConductance_vertexWeight_zero]
    change 0 < (((μC Set.univ)⁻¹ : ℝ≥0∞) • μC) ({0} : Set ℕ)
    rw [Measure.smul_apply]
    exact ENNReal.mul_pos (by simp [hmass_ne_zero, hmass_lt_top.ne]) hμC0_pos.ne'
  -- Proof comment: an invariant distribution with positive singleton mass at `0` closes positive
  -- recurrence of the boundary state.
  let κ : ℕ → Kernel ℕ ℕ :=
    fun n ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n
  have hπ_inv_pow : Kernel.Invariant (κ 1) (π : Measure ℕ) := by
    simpa [κ] using hπ_inv
  exact
    isPositiveRecurrentState_of_invariantDistribution_singleton_pos
      (κ := κ) (P := P) (X := X) (y := 0) hπ_inv_pow hπ0_pos

/-- Helper for Exercise 19.6.1: the tail `Set.Ici (n + 1)` splits into the boundary singleton
`{n + 1}` and the next tail `Set.Ici (n + 2)`. -/
private theorem measure_Ici_succ_eq_singleton_add_Ici
    (ν : Measure ℕ) (n : ℕ) :
    ν (Set.Ici (n + 1)) = ν ({n + 1} : Set ℕ) + ν (Set.Ici (n + 2)) := by
  have hsplit : Set.Ici (n + 1) = ({n + 1} : Set ℕ) ∪ Set.Ici (n + 2) := by
    ext x
    constructor
    · intro hx
      by_cases hxEq : x = n + 1
      · exact Or.inl hxEq
      · exact Or.inr <|
          Nat.succ_le_of_lt
            (lt_of_le_of_ne hx (by simpa [eq_comm] using hxEq))
    · rintro (hx | hx)
      · have hx' : x = n + 1 := by simpa using hx
        simpa [hx'] using Nat.lt_succ_self n
      · exact le_trans (Nat.le_succ (n + 1)) hx
  have hdisj : Disjoint ({n + 1} : Set ℕ) (Set.Ici (n + 2)) := by
    refine Set.disjoint_left.2 ?_
    intro x hxSingleton hxTail
    have : x = n + 1 := by simpa using hxSingleton
    have : n + 2 ≤ n + 1 := by simpa [this] using hxTail
    omega
  -- Proof comment: the two pieces are disjoint measurable atoms of the discrete tail.
  rw [hsplit, measure_union hdisj MeasurableSet.of_discrete]

/-- Helper for Exercise 19.6.1: on `ℕ`, the total mass of a measure is the sum of its singleton
masses. -/
private theorem measure_univ_eq_tsum_singleton
    (ν : Measure ℕ) :
    ν Set.univ = ∑' n : ℕ, ν ({n} : Set ℕ) := by
  -- Proof comment: this is the standard countable-atomic decomposition of a measure on `ℕ`.
  simpa using
    (Measure.tsum_indicator_apply_singleton (μ := ν) Set.univ MeasurableSet.univ).symm

/-- Helper for Exercise 19.6.1: the tail `Set.Ici n` is the singleton expansion of the restricted
measure to that tail. -/
private theorem measure_Ici_eq_tsum_singleton
    (ν : Measure ℕ) (n : ℕ) :
    ν (Set.Ici n) = ∑' k : ℕ, if n ≤ k then ν ({k} : Set ℕ) else 0 := by
  -- Proof comment: rewrite the tail mass as the total mass of the restricted measure and then
  -- expand that restricted measure into its singleton atoms.
  calc
    ν (Set.Ici n) = (ν.restrict (Set.Ici n)) Set.univ := by
      rw [Measure.restrict_apply MeasurableSet.univ]
      simp
    _ = ∑' k : ℕ, (ν.restrict (Set.Ici n)) ({k} : Set ℕ) := by
      exact measure_univ_eq_tsum_singleton (ν.restrict (Set.Ici n))
    _ = ∑' k : ℕ, if n ≤ k then ν ({k} : Set ℕ) else 0 := by
      refine tsum_congr fun k ↦ ?_
      by_cases hk : n ≤ k
      · rw [if_pos hk, Measure.restrict_apply (measurableSet_singleton k)]
        simp [hk]
      · rw [if_neg hk, Measure.restrict_apply (measurableSet_singleton k)]
        simp [hk]

/-- Helper for Exercise 19.6.1: on the countable discrete state space `ℕ`, invariance of the
blocked half-line kernel is equivalent to the singleton balance equations. -/
private theorem blockedAtZeroKernelInvariant_iff_singleton
    {W : HalfLineRandomEnvironment} (μ : Measure ℕ) :
    Kernel.Invariant (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W)) μ ↔
      ∀ x : ℕ,
        ∑' y : ℕ, μ ({y} : Set ℕ) * blockedAtZeroRandomEnvironmentTransitionMatrix W y x =
          μ ({x} : Set ℕ) := by
  constructor
  · intro hμ x
    -- Proof comment: evaluate the invariant-measure identity on the singleton `{x}`.
    have hx := congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) hμ.def
    simpa [comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx
  · intro hμ
    rw [Kernel.Invariant]
    refine Measure.ext_of_singleton fun x ↦ ?_
    -- Proof comment: singleton balance determines the full measure on the discrete state space.
    simpa [comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hμ x

/-- Helper for Exercise 19.6.1: the only states sending mass to `0` are `0` itself and `1`. -/
private theorem blockedAtZeroRandomEnvironmentTransitionMatrix_to_zero
    (W : HalfLineRandomEnvironment) (y : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W y 0 =
      if y = 0 then (((1 : ℝ≥0) - W.rightJumpProb 0 : ℝ≥0) : ℝ≥0∞)
      else if y = 1 then (((1 : ℝ≥0) - W.rightJumpProb 1 : ℝ≥0) : ℝ≥0∞)
      else 0 := by
  cases y with
  | zero =>
      simp [blockedAtZeroRandomEnvironmentTransitionMatrix_zero_self]
  | succ n =>
      cases n with
      | zero =>
          simpa using blockedAtZeroRandomEnvironmentTransitionMatrix_left W 0
      | succ n =>
          simp [blockedAtZeroRandomEnvironmentTransitionMatrix_succ]

/-- Helper for Exercise 19.6.1: the only states sending mass to `n + 1` are `n` and `n + 2`. -/
private theorem blockedAtZeroRandomEnvironmentTransitionMatrix_to_succ
    (W : HalfLineRandomEnvironment) (n y : ℕ) :
    blockedAtZeroRandomEnvironmentTransitionMatrix W y (n + 1) =
      if y = n then (W.rightJumpProb n : ℝ≥0∞)
      else if y = n + 2 then (((1 : ℝ≥0) - W.rightJumpProb (n + 2) : ℝ≥0) : ℝ≥0∞)
      else 0 := by
  by_cases hy_left : y = n
  ·
    subst y
    cases n with
    | zero =>
        simpa using blockedAtZeroRandomEnvironmentTransitionMatrix_zero_one W
    | succ n =>
        simpa [Nat.add_assoc] using blockedAtZeroRandomEnvironmentTransitionMatrix_right W n
  · by_cases hy_right : y = n + 2
    · subst y
      simpa [Nat.add_assoc] using blockedAtZeroRandomEnvironmentTransitionMatrix_left W (n + 1)
    · cases y with
      | zero =>
          have hn : n ≠ 0 := by
            intro hn
            exact hy_left hn.symm
          simp [blockedAtZeroRandomEnvironmentTransitionMatrix, hy_left, hy_right, hn]
      | succ k =>
          rw [blockedAtZeroRandomEnvironmentTransitionMatrix_succ]
          by_cases hleft_zero : n = k + 1
          · exact False.elim (hy_left hleft_zero.symm)
          · by_cases hright_zero : k = n + 1
            · exact False.elim <| hy_right <| by omega
            · have hleft_shift : n + 1 ≠ k := by
                intro hk
                apply hy_right
                omega
              have hright_shift : k + 1 ≠ n := hy_left
              simp [hleft_zero, hright_zero, hleft_shift, hright_shift]

/-- Helper for Exercise 19.6.1: invariance on the tail `Set.Ici (n + 1)` yields the local flow
identity across the edge `{n, n + 1}`. -/
private theorem blockedAtZeroInvariantDistribution_flow
    {W : HalfLineRandomEnvironment} (π : ProbabilityMeasure ℕ)
    (hπ :
      Kernel.Invariant
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
        (π : Measure ℕ))
    (n : ℕ) :
    (π : Measure ℕ) ({n} : Set ℕ) * W.rightJumpProb n =
      (π : Measure ℕ) ({n + 1} : Set ℕ) *
        ((((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)) := by
  let μ : ℕ → ℝ≥0∞ := fun k ↦ (π : Measure ℕ) ({k} : Set ℕ)
  let q : ℕ → ℝ≥0∞ :=
    fun k ↦ (((1 : ℝ≥0) - W.rightJumpProb k : ℝ≥0) : ℝ≥0∞)
  have hbal :=
    (blockedAtZeroKernelInvariant_iff_singleton (W := W) (μ := (π : Measure ℕ))).1 hπ
  have hq_add_p : ∀ k : ℕ, q k + W.rightJumpProb k = 1 := by
    intro k
    have hprob : (W.rightJumpProb k : ℝ≥0∞) ≤ 1 := by
      exact_mod_cast W.rightJumpProb_le_one k
    -- Proof comment: the blocked left- and right-jump probabilities at a fixed site sum to `1`.
    simpa [q, add_comm] using
      (add_tsub_cancel_of_le hprob :
        W.rightJumpProb k + ((1 : ℝ≥0∞) - W.rightJumpProb k) = 1)
  have hmass_split : ∀ k : ℕ, μ k * q k + μ k * W.rightJumpProb k = μ k := by
    intro k
    -- Proof comment: multiplying the local probability normalization by the singleton mass
    -- recovers the mass itself.
    calc
      μ k * q k + μ k * W.rightJumpProb k
          = μ k * (q k + W.rightJumpProb k) := by rw [← mul_add]
      _ = μ k * 1 := by rw [hq_add_p k]
      _ = μ k := by rw [mul_one]
  have hmass_lt_top : ∀ k : ℕ, μ k < ∞ := by
    intro k
    exact lt_of_le_of_ne le_top (measure_ne_top _ _)
  have hzero_balance : μ 0 * q 0 + μ 1 * q 1 = μ 0 := by
    have hraw :
        ∑' y : ℕ, μ y * (if y = 0 then q 0 else if y = 1 then q 1 else 0) = μ 0 := by
      -- Proof comment: singleton balance at `0` collapses to the self-loop at `0` and the
      -- incoming left jump from `1`.
      simpa [μ, q, blockedAtZeroRandomEnvironmentTransitionMatrix_to_zero] using hbal 0
    rw [ENNReal.tsum_eq_add_tsum_ite 0, ENNReal.tsum_eq_add_tsum_ite 1] at hraw
    have htail :
        (∑' x : ℕ,
          if x = 1 then 0
          else if x = 0 then 0
          else if x = 0 then μ x * q 0 else if x = 1 then μ x * q 1 else 0) = 0 := by
      refine ENNReal.tsum_eq_zero.2 ?_
      intro x
      by_cases hx1 : x = 1
      · simp [hx1]
      · by_cases hx0 : x = 0
        · simp [hx1, hx0]
        · simp [hx1, hx0]
    simpa [htail, add_assoc] using hraw
  have hsucc_balance : ∀ m : ℕ, μ m * W.rightJumpProb m + μ (m + 2) * q (m + 2) = μ (m + 1) := by
    intro m
    have hraw :
        ∑' y : ℕ,
          μ y *
              (if y = m then (W.rightJumpProb m : ℝ≥0∞)
                else if y = m + 2 then q (m + 2) else 0) =
            μ (m + 1) := by
      -- Proof comment: singleton balance at `m + 1` collapses to the two nearest incoming
      -- neighbors `m` and `m + 2`.
      simpa [μ, q, blockedAtZeroRandomEnvironmentTransitionMatrix_to_succ] using hbal (m + 1)
    rw [ENNReal.tsum_eq_add_tsum_ite m, ENNReal.tsum_eq_add_tsum_ite (m + 2)] at hraw
    have htail :
        (∑' x : ℕ,
          if x = m + 2 then 0
          else if x = m then 0
          else if x = m then μ x * (W.rightJumpProb m : ℝ≥0∞)
          else if x = m + 2 then μ x * q (m + 2) else 0) = 0 := by
      refine ENNReal.tsum_eq_zero.2 ?_
      intro x
      by_cases hx2 : x = m + 2
      · simp [hx2]
      · by_cases hxm : x = m
        · simp [hx2, hxm]
        · simp [hx2, hxm]
    simpa [htail, add_assoc] using hraw
  induction n with
  | zero =>
      have hsum_eq :
          μ 0 * q 0 + μ 1 * q 1 = μ 0 * q 0 + μ 0 * W.rightJumpProb 0 := by
        calc
          μ 0 * q 0 + μ 1 * q 1 = μ 0 := hzero_balance
          _ = μ 0 * q 0 + μ 0 * W.rightJumpProb 0 := by
                simpa [add_comm] using (hmass_split 0).symm
      have hq0_lt_top : q 0 < ∞ := by
        change ((1 : ℝ≥0∞) - W.rightJumpProb 0) < ∞
        exact lt_of_le_of_ne le_top (ENNReal.sub_ne_top (by simp))
      have hcommon_ne_top : μ 0 * q 0 ≠ ∞ := (ENNReal.mul_lt_top (hmass_lt_top 0) hq0_lt_top).ne
      -- Proof comment: cancel the common finite boundary self-loop term to isolate the boundary
      -- edge flow.
      change μ 0 * W.rightJumpProb 0 = μ 1 * q 1
      exact ((ENNReal.add_right_inj hcommon_ne_top).1 hsum_eq).symm
  | succ n ih =>
      have hsum_eq :
          μ (n + 1) * q (n + 1) + μ (n + 2) * q (n + 2) =
            μ (n + 1) * q (n + 1) + μ (n + 1) * W.rightJumpProb (n + 1) := by
        calc
          μ (n + 1) * q (n + 1) + μ (n + 2) * q (n + 2)
              = μ n * W.rightJumpProb n + μ (n + 2) * q (n + 2) := by rw [← ih]
          _ = μ (n + 1) := hsucc_balance n
          _ = μ (n + 1) * q (n + 1) + μ (n + 1) * W.rightJumpProb (n + 1) := by
                simpa [add_comm] using (hmass_split (n + 1)).symm
      have hcommon_ne_top : μ (n + 1) * q (n + 1) ≠ ∞ := by
        have hq_lt_top : q (n + 1) < ∞ := by
          change ((1 : ℝ≥0∞) - W.rightJumpProb (n + 1)) < ∞
          exact lt_of_le_of_ne le_top (ENNReal.sub_ne_top (by simp))
        exact (ENNReal.mul_lt_top (hmass_lt_top (n + 1)) hq_lt_top).ne
      -- Proof comment: cancel the common finite interior stay-left term to propagate the local
      -- edge flow recursion from `n` to `n + 1`.
      change μ (n + 1) * W.rightJumpProb (n + 1) = μ (n + 2) * q (n + 2)
      exact ((ENNReal.add_right_inj hcommon_ne_top).1 hsum_eq).symm

/-- Helper for Exercise 19.6.1: the blocked conductance row weights satisfy the same local flow
identity as an invariant distribution. -/
private theorem blockedAtZeroVertexWeight_flow
    {W : HalfLineRandomEnvironment} (hW : W.IsElliptic) (n : ℕ) :
    conductance (blockedAtZeroConductance W) n * W.rightJumpProb n =
      conductance (blockedAtZeroConductance W) (n + 1) *
        ((((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)) := by
  have hforward :
      conductance (blockedAtZeroConductance W) n * W.rightJumpProb n =
        blockedAtZeroEdgeConductance W n := by
    -- Proof comment: the forward blocked jump from `n` to `n + 1` is the conductance edge
    -- `{n, n + 1}` normalized by the row weight at `n`.
    calc
      conductance (blockedAtZeroConductance W) n * W.rightJumpProb n
          =
            conductance (blockedAtZeroConductance W) n *
              conductanceTransitionMatrix (blockedAtZeroConductance W) n (n + 1) := by
                rw [← blockedAtZeroTransition_eq_conductanceTransitionMatrix hW n (n + 1),
                  blockedAtZeroRandomEnvironmentTransitionMatrix_forward]
      _ = blockedAtZeroConductance W n (n + 1) := by
            simpa using
              conductance_mul_transitionMatrix
                (C := blockedAtZeroConductance W)
                (blockedAtZeroConductance_vertexWeight_lt_top hW)
                (blockedAtZeroConductance_vertexWeight_pos hW)
                n (n + 1)
      _ = blockedAtZeroEdgeConductance W n := by
            rw [blockedAtZeroConductance_forward]
  have hbackward :
      conductance (blockedAtZeroConductance W) (n + 1) *
          ((((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)) =
        blockedAtZeroEdgeConductance W n := by
    -- Proof comment: the backward blocked jump from `n + 1` to `n` is the same conductance edge
    -- `{n, n + 1}` normalized by the row weight at `n + 1`.
    calc
      conductance (blockedAtZeroConductance W) (n + 1) *
          ((((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞))
          =
            conductance (blockedAtZeroConductance W) (n + 1) *
              conductanceTransitionMatrix (blockedAtZeroConductance W) (n + 1) n := by
                rw [← blockedAtZeroTransition_eq_conductanceTransitionMatrix hW (n + 1) n,
                  blockedAtZeroRandomEnvironmentTransitionMatrix_left]
      _ = blockedAtZeroConductance W (n + 1) n := by
            simpa using
              conductance_mul_transitionMatrix
                (C := blockedAtZeroConductance W)
                (blockedAtZeroConductance_vertexWeight_lt_top hW)
                (blockedAtZeroConductance_vertexWeight_pos hW)
                (n + 1) n
      _ = blockedAtZeroEdgeConductance W n := by
            rw [blockedAtZeroConductance_backward]
  exact hforward.trans hbackward.symm

/-- Helper for Exercise 19.6.1: the singleton masses of an invariant distribution are its mass at
`0` times the blocked conductance vertex weights. -/
private theorem blockedAtZeroInvariantDistribution_apply_singleton_eq_zeroMass_mulVertexWeight
    {W : HalfLineRandomEnvironment} (π : ProbabilityMeasure ℕ)
    (hπ :
      Kernel.Invariant
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
        (π : Measure ℕ))
    (hW : W.IsElliptic) :
    ∀ n : ℕ,
      (π : Measure ℕ) ({n} : Set ℕ) =
        ((π : Measure ℕ) ({0} : Set ℕ)) * conductance (blockedAtZeroConductance W) n := by
  let μ : ℕ → ℝ≥0∞ := fun k ↦ (π : Measure ℕ) ({k} : Set ℕ)
  have hμ0 : μ 0 = (π : Measure ℕ) ({0} : Set ℕ) := rfl
  intro n
  induction n with
  | zero =>
      -- Proof comment: both singleton-mass and conductance profiles are normalized to `1` at
      -- the boundary state `0`.
      simpa [μ, blockedAtZeroConductance_vertexWeight_zero]
  | succ n ih =>
      let q : ℝ≥0∞ := (((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)
      have ihμ :
          μ n = ((π : Measure ℕ) ({0} : Set ℕ)) * conductance (blockedAtZeroConductance W) n := by
        simpa [μ] using ih
      have hflow_mass :
          μ n * W.rightJumpProb n = μ (n + 1) * q :=
        by simpa [μ, q] using blockedAtZeroInvariantDistribution_flow (π := π) hπ n
      have hflow_vertex :
          conductance (blockedAtZeroConductance W) n * W.rightJumpProb n =
            conductance (blockedAtZeroConductance W) (n + 1) * q :=
        by simpa [q] using blockedAtZeroVertexWeight_flow (W := W) hW n
      have hfactor :
          μ (n + 1) * q =
            (((π : Measure ℕ) ({0} : Set ℕ)) *
              conductance (blockedAtZeroConductance W) (n + 1)) * q := by
        -- Proof comment: both singleton masses and conductance vertex weights satisfy the same
        -- one-step edge flow equation, so the induction hypothesis transports through the common
        -- factor `q`.
        calc
          μ (n + 1) * q = μ n * W.rightJumpProb n := hflow_mass.symm
          _ = (((π : Measure ℕ) ({0} : Set ℕ)) *
                conductance (blockedAtZeroConductance W) n) * W.rightJumpProb n := by
                  rw [ihμ]
          _ = ((π : Measure ℕ) ({0} : Set ℕ)) *
                (conductance (blockedAtZeroConductance W) n * W.rightJumpProb n) := by
                  ac_rfl
          _ = ((π : Measure ℕ) ({0} : Set ℕ)) *
                (conductance (blockedAtZeroConductance W) (n + 1) * q) := by
                  rw [hflow_vertex]
          _ = (((π : Measure ℕ) ({0} : Set ℕ)) *
                conductance (blockedAtZeroConductance W) (n + 1)) * q := by
                  ac_rfl
      have hq_pos : 0 < q := by
        have hq_pos' :
            0 <
              ((((1 : ℝ≥0) - W.rightJumpProb (n + 1) : ℝ≥0) : ℝ≥0∞)) := by
          exact_mod_cast (tsub_pos_iff_lt.2 (hW.lt_one (n + 1)))
        simpa [q] using hq_pos'
      have hq_ne_top : q ≠ ∞ := by
        simp [q]
      have hfactor' :
          q * μ (n + 1) =
            q *
              (((π : Measure ℕ) ({0} : Set ℕ)) *
                conductance (blockedAtZeroConductance W) (n + 1)) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hfactor
      -- Proof comment: cancel the common positive finite left-jump factor to identify the next
      -- singleton mass with the next conductance vertex weight.
      simpa [μ] using (ENNReal.mul_right_inj (ne_of_gt hq_pos) hq_ne_top).mp hfactor'

/-- Exercise 19.6.1: positive recurrence at the blocked boundary forces the blocked
edge-conductance series to be summable. -/
-- Route correction: the stale tail-set normalization at `Set.Ici (n + 1)` kept collapsing into
-- the wrong `Measure.sum_apply` normal form, so the converse direction now works purely with
-- singleton balance equations and the matching conductance recursion.
private theorem blockedAtZeroConductanceSeries_lt_top_of_stateZeroPositiveRecurrent
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic)
    (hpos0 : IsPositiveRecurrentState P X 0) :
    (∑' n, blockedAtZeroEdgeConductance W n) < ∞ := by
  rcases
    existsInvariantDistributionAtPositiveRecurrentState
      (κ := fun n : ℕ ↦
        discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      (P := P) (X := X) 0 hpos0 with
    ⟨π, hπ, hπ0_pos⟩
  have hπ_one :
      Kernel.Invariant
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W))
        (π : Measure ℕ) := by
    simpa using hπ
  have hsingleton :
      ∀ n : ℕ,
        (π : Measure ℕ) ({n} : Set ℕ) =
          ((π : Measure ℕ) ({0} : Set ℕ)) * conductance (blockedAtZeroConductance W) n :=
    blockedAtZeroInvariantDistribution_apply_singleton_eq_zeroMass_mulVertexWeight
      (π := π) hπ_one hW
  have hscaled_univ :
      ((π : Measure ℕ) ({0} : Set ℕ)) *
          conductanceMeasure (blockedAtZeroConductance W) Set.univ =
        1 := by
    -- Proof comment: summing the singleton identity over all states identifies the invariant
    -- probability mass of `π` with the boundary mass times the total conductance mass.
    calc
      ((π : Measure ℕ) ({0} : Set ℕ)) *
          conductanceMeasure (blockedAtZeroConductance W) Set.univ
          = ((π : Measure ℕ) ({0} : Set ℕ)) *
              ∑' n : ℕ, conductance (blockedAtZeroConductance W) n := by
                rw [blockedAtZeroConductanceMeasure_univ_eq_tsum]
      _ = ∑' n : ℕ,
            ((π : Measure ℕ) ({0} : Set ℕ)) *
              conductance (blockedAtZeroConductance W) n := by
              rw [ENNReal.tsum_mul_left]
      _ = ∑' n : ℕ, (π : Measure ℕ) ({n} : Set ℕ) := by
            refine tsum_congr fun n ↦ ?_
            symm
            simpa using hsingleton n
      _ = (π : Measure ℕ) Set.univ := by
            rw [measure_univ_eq_tsum_singleton]
      _ = 1 := by simp
  have hmeasure_lt_top :
      conductanceMeasure (blockedAtZeroConductance W) Set.univ < ∞ := by
    by_cases htop : conductanceMeasure (blockedAtZeroConductance W) Set.univ = ∞
    · rw [htop, ENNReal.mul_top hπ0_pos.ne'] at hscaled_univ
      simp at hscaled_univ
    · exact lt_of_le_of_ne le_top htop
  -- Proof comment: once the total conductance measure is finite, the earlier conductance-mass
  -- criterion turns that directly into summability of the edge-conductance series.
  exact blockedAtZeroConductanceSeries_lt_top_of_conductanceMeasure_univ_lt_top W hmeasure_lt_top

/-- Helper for Exercise 19.6.1: positive recurrence at the blocked boundary propagates to every
state because every positive state is hit from `0` with positive probability. -/
private theorem blockedAtZeroAllStatesPositiveRecurrent_of_stateZeroPositiveRecurrent
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic)
    (hpos0 : IsPositiveRecurrentState P X 0) :
    ∀ x : ℕ, IsPositiveRecurrentState P X x := by
  intro x
  cases x with
  | zero =>
      -- Proof comment: the boundary state is the given positive recurrent base case.
      simpa using hpos0
  | succ n =>
      have hhit :
          0 < (F[P, X]) 0 (n + 1) :=
        blockedAtZeroEverHitsProbability_pos_from_zero
          (P := P) (X := X) (W := W) hW n
      -- Proof comment: Exercise 17.4.1 transfers positive recurrence along positive
      -- communication from `0`.
      exact
        isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
          (κ := fun m : ℕ ↦
            discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ m)
          (P := P) (X := X) hpos0 hhit

/-- Helper for Exercise 19.6.1: if the blocked boundary state is not positive recurrent, then no
state can be positive recurrent because every positive state hits `0` with positive probability. -/
private theorem blockedAtZeroNoStatesPositiveRecurrent_of_not_stateZeroPositiveRecurrent
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic)
    (hnotpos0 : ¬ IsPositiveRecurrentState P X 0) :
    ∀ x : ℕ, ¬ IsPositiveRecurrentState P X x := by
  intro x hx
  cases x with
  | zero =>
      exact hnotpos0 hx
  | succ n =>
      have hhit :
          0 < (F[P, X]) (n + 1) 0 :=
        blockedAtZeroEverHitsProbability_pos_to_zero
          (P := P) (X := X) (W := W) hW n
      have hpos0 :
          IsPositiveRecurrentState P X 0 :=
        isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
          (κ := fun m : ℕ ↦
            discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ m)
          (P := P) (X := X) (x := n + 1) (y := 0) hx hhit
      exact hnotpos0 hpos0

/-- Helper for Exercise 19.6.1: for the blocked half-line chain, state `0` is positive recurrent
exactly when the total conductance mass is finite. -/
theorem blockedAtZeroStateZeroPositiveRecurrent_iff_summableConductance
    {W : HalfLineRandomEnvironment}
    {P : ℕ → ProbabilityMeasure Ξ} {X : ℕ → Ξ → ℕ}
    [IsMarkovProcessRealization
      (fun n : ℕ ↦ discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix W) ^ n)
      P X]
    (hW : W.IsElliptic) :
    IsPositiveRecurrentState P X 0 ↔
      (∑' n, blockedAtZeroEdgeConductance W n) < ∞ := by
  constructor
  · -- Proof comment: a positive recurrent boundary state yields an invariant law that forces the
    -- reversible conductance measure to have finite total mass.
    exact
      blockedAtZeroConductanceSeries_lt_top_of_stateZeroPositiveRecurrent
        (P := P) (X := X) (W := W) hW
  · -- Proof comment: finite total conductance mass normalizes directly to an invariant
    -- distribution with positive mass at `0`.
    exact
      blockedAtZeroStateZeroPositiveRecurrent_of_conductanceSeries_lt_top
        (P := P) (X := X) (W := W) hW

-- Proof sketch: this is the blocked-half-line analogue of the right-transient branch of
-- Theorem 19.35. Negative mean `E[log ρ₀]` yields almost-sure rightward drift, and blocking the
-- forbidden jump from `0` to `-1` does not create recurrent traps, so every state of the quenched
-- half-line chain is transient.
/-- Part (1) of Exercise 19.6.1: for the half-line random walk in random environment with blocked
boundary
at `0`, if
`E[log ρ₀] < 0` and `E[|log ρ₀|] < ∞`, then for almost every environment every state is
transient. -/
theorem ae_allStatesTransient_of_integral_logRatio_lt_zero_blockedAtZero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω))
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ < 0) :
    ∀ᵐ ω ∂μ, ∀ x : ℕ, IsTransientState (P ω) (X ω) x := by
  filter_upwards
    [hW.ae_elliptic,
      ae_blockedAtZeroResistanceSeries_lt_top_of_integral_logRatio_lt_zero
        (μ := μ) (W := W) hW hlog hmean] with ω hω hω_series x
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
        (P ω) (X ω) :=
    hreal ω
  letI :
      Kernel.IsIrreducible (Measure.count : Measure ℕ)
        (discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω))) :=
    blockedAtZeroKernel_isIrreducible (W := W ω) hω
  rcases
      irreducibleMarkovChain_recurrent_or_transient_of_discreteMatrixKernel_isIrreducible
        (p := blockedAtZeroRandomEnvironmentTransitionMatrix (W ω))
        (P := P ω) (X := X ω) with hrec | htrans
  · have hseries_eq_top :
        (∑' n, (blockedAtZeroEdgeConductance (W ω) n)⁻¹) = ∞ :=
      (blockedAtZeroStateZeroRecurrent_iff_resistanceSeries
        (P := P ω) (X := X ω) (W := W ω) hω).1 (hrec 0)
    exact False.elim ((ne_of_lt hω_series) hseries_eq_top)
  · exact htrans x

-- Proof sketch: at the critical value `E[log ρ₀] = 0`, the blocked walk remains recurrent but has
-- infinite expected return time; staying at `0` blocks escape to `-∞` without
-- creating a finite invariant law, so almost every quenched chain is null recurrent at every
-- state.
/-- Part (2) of Exercise 19.6.1: for the half-line random walk in random environment with blocked
boundary
at `0`, if
`E[log ρ₀] = 0` and `E[|log ρ₀|] < ∞`, then for almost every environment every state is null
recurrent. -/
theorem ae_allStatesNullRecurrent_of_integral_logRatio_eq_zero_blockedAtZero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω))
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : ∫ ω, logρ₊[W](0) ω ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∀ x : ℕ, IsNullRecurrentState (P ω) (X ω) x := by
  filter_upwards
    [hW.ae_elliptic,
      ae_blockedAtZeroResistanceSeries_eq_top_of_integral_logRatio_eq_zero
        (μ := μ) (W := W) hW hlog hmean,
      ae_blockedAtZeroConductanceSeries_eq_top_of_integral_logRatio_eq_zero
        (μ := μ) (W := W) hW hlog hmean] with ω hω hω_resistance hω_conductance x
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
        (P ω) (X ω) :=
    hreal ω
  have hrec0 : IsRecurrentState (P ω) (X ω) 0 :=
    (blockedAtZeroStateZeroRecurrent_iff_resistanceSeries
      (P := P ω) (X := X ω) (W := W ω) hω).2 hω_resistance
  have hallRec :
      ∀ y : ℕ, IsRecurrentState (P ω) (X ω) y :=
    blockedAtZeroAllStatesRecurrent_of_stateZeroRecurrent
      (P := P ω) (X := X ω) (W := W ω) hω hrec0
  have hnotPos0 : ¬ IsPositiveRecurrentState (P ω) (X ω) 0 := by
    intro hpos0
    have hcond_lt_top :
        (∑' n, blockedAtZeroEdgeConductance (W ω) n) < ∞ :=
      (blockedAtZeroStateZeroPositiveRecurrent_iff_summableConductance
        (P := P ω) (X := X ω) (W := W ω) hω).1 hpos0
    exact (ne_of_lt hcond_lt_top) hω_conductance
  have hnoPos :
      ∀ y : ℕ, ¬ IsPositiveRecurrentState (P ω) (X ω) y :=
    blockedAtZeroNoStatesPositiveRecurrent_of_not_stateZeroPositiveRecurrent
      (P := P ω) (X := X ω) (W := W ω) hω hnotPos0
  -- Proof comment: the critical regime combines recurrence with failure of positive recurrence at
  -- every state, which is exactly null recurrence.
  exact ⟨hallRec x, hnoPos x⟩

-- Proof sketch: when `E[log ρ₀] > 0`, the half-line walk has leftward bias toward the boundary;
-- blocking at `0` traps that drift and yields finite return times, hence almost every quenched
-- half-line chain is positive recurrent.
/-- Part (3) of Exercise 19.6.1: for the half-line random walk in random environment with blocked
boundary
at `0`, if
`E[log ρ₀] > 0` and `E[|log ρ₀|] < ∞`, then for almost every environment every state is positive
recurrent. -/
theorem ae_allStatesPositiveRecurrent_of_integral_logRatio_gt_zero_blockedAtZero
    (hW : IsHalfLineSolomonEnvironmentLaw μ W)
    (hreal :
      ∀ ω,
        IsMarkovProcessRealization
          (fun n : ℕ ↦
            discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
          (P ω) (X ω))
    (hlog : Integrable (logρ₊[W](0)) μ)
    (hmean : 0 < ∫ ω, logρ₊[W](0) ω ∂μ) :
    ∀ᵐ ω ∂μ, ∀ x : ℕ, IsPositiveRecurrentState (P ω) (X ω) x := by
  filter_upwards
    [hW.ae_elliptic,
      ae_blockedAtZeroConductanceSeries_lt_top_of_integral_logRatio_gt_zero
        (μ := μ) (W := W) hW hlog hmean] with ω hω hω_series x
  letI :
      IsMarkovProcessRealization
        (fun n : ℕ ↦
          discreteMatrixKernel (blockedAtZeroRandomEnvironmentTransitionMatrix (W ω)) ^ n)
        (P ω) (X ω) :=
    hreal ω
  have hpos0 : IsPositiveRecurrentState (P ω) (X ω) 0 :=
    (blockedAtZeroStateZeroPositiveRecurrent_iff_summableConductance
      (P := P ω) (X := X ω) (W := W ω) hω).2 hω_series
  exact
    blockedAtZeroAllStatesPositiveRecurrent_of_stateZeroPositiveRecurrent
      (P := P ω) (X := X ω) (W := W ω) hω hpos0 x

end

end ProbabilityTheory

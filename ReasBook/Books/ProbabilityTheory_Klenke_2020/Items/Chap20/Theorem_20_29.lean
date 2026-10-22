/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_46
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_51
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Example_20_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24

open MeasureTheory ProbabilityTheory
open Filter
open scoped ENNReal ProbabilityTheory Topology symmDiff

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Countable E]
variable {Ω : Type v} [MeasurableSpace Ω]

local instance : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

/-- The stationary law `P_π` obtained by mixing the laws `P x` against the initial distribution
`π`. -/
def stationaryLaw (P : E → ProbabilityMeasure Ω) (π : ProbabilityMeasure E) : Measure Ω :=
  (Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) ∘ₘ (π : Measure E)

instance (P : E → ProbabilityMeasure Ω) :
    IsMarkovKernel (Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) := by
  refine ⟨fun x ↦ ?_⟩
  change IsProbabilityMeasure (P x : Measure Ω)
  infer_instance

instance (P : E → ProbabilityMeasure Ω) (π : ProbabilityMeasure E) :
    IsProbabilityMeasure (stationaryLaw P π) := by
  dsimp [stationaryLaw]
  infer_instance

/-- The stationary law obtained by mixing the laws `P x` against `π` is exactly the weighted sum
`∑ x, π{x} P x`. -/
theorem stationaryLaw_eq_sum
    (P : E → ProbabilityMeasure Ω) (π : ProbabilityMeasure E) :
    stationaryLaw P π =
      Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω) := by
  simpa [stationaryLaw] using
    (Measure.comp_eq_sum_of_countable :
      ((Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) : Kernel E Ω) ∘ₘ (π : Measure E) =
        Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) •
          (Kernel.ofFunOfCountable fun x ↦ (P x : Measure Ω)) x)

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

/-- Helper for Theorem 20.29: the trajectory map `ω ↦ (n ↦ X n ω)` is measurable. -/
lemma measurable_stationaryTrajectoryMap
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    Measurable (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  -- Proof comment: coordinatewise measurability of the realization upgrades to measurability of
  -- the full trajectory map into the product path space.
  refine measurable_pi_lambda _ fun n ↦ ?_
  exact hReal.measurable_process n

/-- Helper for Theorem 20.29: pulling a shifted path event back along the trajectory map is the
same as pulling back the explicit shifted trajectory event. -/
lemma trajectoryPreimage_iterateTail_eq_futurePathPreimage
    (n : ℕ) (B : Set (Stream' E)) :
    (fun ω : Ω ↦ fun k : ℕ ↦ X k ω) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B) =
      (fun ω : Ω ↦ fun k : ℕ ↦ X (n + k) ω) ⁻¹' B := by
  -- Proof comment: `Stream'.tail^[n]` drops the first `n` coordinates, while `futurePath X n`
  -- records exactly the shifted realization `k ↦ X (n + k)`.
  ext ω
  change ((Stream'.tail^[n]) (fun k : ℕ ↦ X k ω)) ∈ B ↔ (fun k : ℕ ↦ X (n + k) ω) ∈ B
  simpa using congrArg (fun f : Stream' E => f ∈ B)
    (funext fun k ↦ tailIterate_apply (E := E) n (fun j : ℕ ↦ X j ω) k)

/-- The canonical path-space law of the stationary Markov process obtained by pushing
`stationaryLaw P π` forward along the trajectory map `ω ↦ (n ↦ X n ω)`. -/
lemma stationaryProcessPathLaw_measure_isProbability
    (p : E → E → ℝ≥0∞) (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (π : ProbabilityMeasure E) :
    IsProbabilityMeasure
      (Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (stationaryLaw P π)) := by
  -- Proof comment: the stationary path law is the pushforward of the probability measure
  -- `stationaryLaw P π` along the measurable trajectory map.
  exact
    Measure.isProbabilityMeasure_map
      (measurable_stationaryTrajectoryMap p P X).aemeasurable

/-- The canonical path-space law of the stationary Markov process obtained by pushing
`stationaryLaw P π` forward along the trajectory map `ω ↦ (n ↦ X n ω)`. -/
def stationaryProcessPathLaw (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (π : ProbabilityMeasure E) : ProbabilityMeasure (Stream' E) :=
  ⟨Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (stationaryLaw P π),
    stationaryProcessPathLaw_measure_isProbability p P X π⟩

/-- The canonical path-space law is, by definition, the pushforward of `stationaryLaw P π` along
the trajectory map of the process. -/
theorem stationaryProcessPathLaw_def (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (π : ProbabilityMeasure E) :
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) =
      Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (stationaryLaw P π) := rfl

/-- Helper for Theorem 20.29: evaluating the stationary path law on a measurable event is the
same as evaluating the stationary realization law on its trajectory preimage. -/
lemma stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
    (π : ProbabilityMeasure E) {A : Set (Stream' E)} (hA : MeasurableSet A) :
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) A =
      stationaryLaw P π ((fun ω : Ω ↦ fun n : ℕ ↦ X n ω) ⁻¹' A) := by
  -- Proof comment: unfold the path law once and apply the defining `Measure.map` formula.
  simpa [stationaryProcessPathLaw_def (p := p) P X π] using
    (Measure.map_apply (μ := stationaryLaw P π)
      (f := fun ω : Ω ↦ fun n : ℕ ↦ X n ω)
      (measurable_stationaryTrajectoryMap p P X) hA)

/-- Helper for Theorem 20.29: shifted path events under the stationary path law can be rewritten
directly as shifted-trajectory events under `stationaryLaw P π`. -/
lemma stationaryProcessPathLaw_iterateTail_apply_eq_stationaryLaw_futurePathPreimage
    (π : ProbabilityMeasure E) (n : ℕ) {B : Set (Stream' E)} (hB : MeasurableSet B) :
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
        ((Stream'.tail^[n]) ⁻¹' B) =
      stationaryLaw P π ((fun ω : Ω ↦ fun k : ℕ ↦ X (n + k) ω) ⁻¹' B) := by
  -- Proof comment: first rewrite the shifted event by the `Measure.map` definition, then use the
  -- trajectory/future-path pullback identity once and for all.
  rw [stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
    (P := P) (X := X) (p := p) π ((measurable_tail (E := E)).iterate n hB)]
  exact congrArg (stationaryLaw P π)
    (trajectoryPreimage_iterateTail_eq_futurePathPreimage (X := X) (n := n) (B := B))

/-- Helper for Theorem 20.29: irreducibility plus an invariant distribution rules out the
transient branch, so the realization is recurrent. -/
lemma recurrent_of_irreducible_invariantDistribution
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) :
    IsRecurrentMarkovChain P X := by
  rcases irreducibleMarkovChain_recurrent_or_transient (p := p) (P := P) (X := X) hirr with
    hrec | htrans
  · exact hrec
  · have hnone :
      invariantDistributions (discreteMatrixKernel p) = ∅ :=
        not_exists_invariantDistribution_of_all_states_transient
          (p := p) (P := P) (X := X) htrans
    have hmem : π ∈ invariantDistributions (discreteMatrixKernel p) :=
      (mem_invariantDistributions_iff (discreteMatrixKernel p) π).2 hπ
    exact False.elim <| by simpa [hnone] using hmem

/-- Helper for Theorem 20.29: irreducibility of the realization upgrades to irreducibility of
`discreteMatrixKernel p` for counting measure. -/
lemma discreteMatrixKernel_isIrreducible_of_irreducibleMarkovChain
    (hirr : IsIrreducibleMarkovChain P X) :
    Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) := by
  refine ⟨?_⟩
  intro A hA hApos x
  have hA_nonempty : A.Nonempty := by
    by_contra hEmpty
    have hAeq : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
    simp [hAeq] at hApos
  rcases hA_nonempty with ⟨y, hyA⟩
  by_cases hxy : x = y
  · subst y
    refine ⟨0, ?_⟩
    -- Proof comment: when the start state already lies in `A`, the time-zero kernel mass is
    -- the Dirac mass of `A` at that state.
    change 0 < (Kernel.id x) A
    simp [Kernel.id_apply, hyA]
  · have hgreen :
        0 < (G[P, X; 1]) x y := by
      exact
        (isIrreducibleMarkovChain_iff_greenFunctionFrom_one_pos_offDiagonal
          (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).1 hirr hxy
    rcases existsPosStepMass_of_greenFunctionFrom_one_pos
        (κ := fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X hgreen with ⟨n, _, hn⟩
    refine ⟨n, lt_of_lt_of_le hn ?_⟩
    -- Proof comment: singleton positivity propagates to every measurable superset containing that
    -- singleton.
    exact measure_mono <| Set.singleton_subset_iff.mpr hyA

/-- Helper for Theorem 20.29: a realization of the powers of `discreteMatrixKernel p` makes `p`
row-stochastic. -/
lemma stochasticMatrix_of_markovProcessRealization
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsStochasticMatrix p := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  let hMarkov : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hReal.semigroup.isMarkovKernel 1
  let _ : IsMarkovKernel (discreteMatrixKernel p) := hMarkov
  intro x
  -- Proof comment: the one-step row measure of `discreteMatrixKernel p` is a probability measure,
  -- so its total mass on `Set.univ` is `1`.
  simpa [discreteMatrixKernel_apply] using
    (measure_univ : (discreteMatrixKernel p x) Set.univ = 1)

/-- Helper for Theorem 20.29: the path-law kernel `x ↦ 𝓛_x[(X n)_n]` of the realization. -/
def realizationPathKernel (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    Kernel E (Stream' E) :=
  Kernel.ofFunOfCountable fun x ↦
    Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (P x : Measure Ω)

instance realizationPathKernel_isMarkovKernel (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsMarkovKernel (realizationPathKernel (p := p) P X) := by
  refine ⟨fun x ↦ ?_⟩
  change IsProbabilityMeasure
    (Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (P x : Measure Ω))
  exact Measure.isProbabilityMeasure_map
    (measurable_stationaryTrajectoryMap p P X).aemeasurable

/-- Helper for Theorem 20.29: the path-law kernel row at `x` is the pushforward of `P x` along
the trajectory map. -/
@[simp] theorem realizationPathKernel_apply
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] (x : E) :
    realizationPathKernel (p := p) P X x =
      Measure.map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) (P x : Measure Ω) := rfl

/-- Helper for Theorem 20.29: the finite prefix of a discrete-time realization up to time `n`. -/
def pastPath (X : ℕ → Ω → E) (n : ℕ) : Ω → Fin (n + 1) → E :=
  fun ω i ↦ X i ω

/-- Helper for Theorem 20.29: evaluating the finite prefix at coordinate `i` reads off `X i`. -/
theorem pastPath_apply
    (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) (i : Fin (n + 1)) :
    pastPath X n ω i = X i ω := rfl

/-- Helper for Theorem 20.29: the finite-history map is measurable once each coordinate of the
realization is measurable. -/
lemma measurable_pastPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (pastPath X n) := by
  -- Proof comment: measurability on the finite product is coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [pastPath] using hX_meas i

/-- Helper for Theorem 20.29: the generated filtration up to time `n` is the pullback
σ-algebra of the finite history map `pastPath X n`. -/
lemma generatedFiltrationSpace_eq_pastPath_comap
    (X : ℕ → Ω → E) (n : ℕ) :
    generatedFiltrationSpace X n = MeasurableSpace.comap (pastPath X n) inferInstance := by
  have hleft :
      MeasurableSpace.comap (pastPath X n) inferInstance ≤ generatedFiltrationSpace X n := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace X n] (fun ω ↦ fun i : Fin (n + 1) ↦ X i ω) := by
      -- Proof comment: every coordinate of the finite history already belongs to the time-`n`
      -- generated filtration.
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact
        le_iSup_of_le i <|
          le_iSup_of_le (show (i : ℕ) ≤ n from Nat.le_of_lt_succ i.2) le_rfl
    exact hPastMeas.comap_le
  have hright :
      generatedFiltrationSpace X n ≤ MeasurableSpace.comap (pastPath X n) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (n + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X n) inferInstance]
          (fun ω ↦ pastPath X n ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (pastPath X n))
    simpa [pastPath, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Theorem 20.29: each finite prefix of the realization is measurable with respect to
the matching generated filtration. -/
lemma measurable_prefixRestriction_in_filtration
    (N : ℕ) :
    Measurable[generatedFiltrationSpace X N]
      (fun ω : Ω ↦ fun i : {i : ℕ // i ≤ N} ↦ X i ω) := by
  -- Proof comment: every prefix coordinate `i ≤ N` already belongs to the time-`N` history
  -- sigma-algebra, so the whole finite prefix map is measurable there.
  rw [@measurable_pi_iff]
  intro i
  refine Measurable.of_comap_le ?_
  exact le_iSup_of_le i.1 <| le_iSup_of_le i.2 le_rfl

/-- Helper for Theorem 20.29: finite-prefix events are measurable at the corresponding history
time. -/
lemma prefixEvent_measurableInFiltration
    {N : ℕ} {A0 : Set (Π i : {i : ℕ // i ≤ N}, E)} (hA0 : MeasurableSet A0) :
    MeasurableSet[generatedFiltrationSpace X N]
      ((fun ω : Ω ↦ fun i : {i : ℕ // i ≤ N} ↦ X i ω) ⁻¹' A0) := by
  -- Proof comment: this is the measurable-prefix map above applied to the target measurable set.
  exact (measurable_prefixRestriction_in_filtration (X := X) N) hA0

/-- Helper for Theorem 20.29: a finite cylinder event depends only on the generated filtration up
to the maximal coordinate in its support. -/
lemma cylinderTrajectoryPreimage_measurableInFiltration
    {s : Finset ℕ} {A0 : Set (s → E)} (hA0 : MeasurableSet A0) :
    let traj : Ω → Stream' E := fun ω : Ω ↦ fun n : ℕ ↦ X n ω
    let N : ℕ := s.sup id
    MeasurableSet[generatedFiltrationSpace X N]
      (traj ⁻¹' MeasureTheory.cylinder s A0) := by
  let traj : Ω → Stream' E := fun ω : Ω ↦ fun n : ℕ ↦ X n ω
  let N : ℕ := s.sup id
  have hrestrict_meas :
      Measurable[generatedFiltrationSpace X N] fun ω : Ω ↦ s.restrict (traj ω) := by
    -- Proof comment: every coordinate in the finite support `s` lies before time `N = s.sup id`.
    rw [@measurable_pi_iff]
    intro i
    have hi_le : (i : ℕ) ≤ N := by
      exact le_trans (by simpa using (Finset.le_sup (f := id) i.2)) le_rfl
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le (i : ℕ) <| le_iSup_of_le hi_le le_rfl
  -- Proof comment: a finite cylinder is the preimage of its base set under the finite restriction.
  simpa [traj, N, MeasureTheory.cylinder] using hA0.preimage hrestrict_meas

/-- Helper for Theorem 20.29: the shifted future path after time `n`, written in Nat-indexed
coordinates. -/
def shiftedPath (X : ℕ → Ω → E) (n : ℕ) : Ω → ℕ → E :=
  fun ω k ↦ X (n + k) ω

/-- Helper for Theorem 20.29: the ordered coordinates of the shifted future path. -/
def shiftedPathCoordinates {m : ℕ} (X : ℕ → Ω → E) (n : ℕ) (t : Fin m → ℕ) :
    Ω → Fin m → E :=
  fun ω i ↦ X (n + t i) ω

/-- Helper for Theorem 20.29: the shifted future path is measurable once each time slice of the
realization is measurable. -/
lemma measurable_shiftedPath
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (shiftedPath X n) := by
  -- Proof comment: every shifted coordinate is just the measurable slice `X (k + n)`.
  refine measurable_pi_lambda _ fun k ↦ ?_
  simpa [shiftedPath] using hX_meas (n + k)

/-- Helper for Theorem 20.29: finite ordered coordinates of the shifted future path are
measurable. -/
lemma measurable_shiftedPathCoordinates {m : ℕ}
    (X : ℕ → Ω → E) (hX_meas : ∀ n, Measurable (X n)) (n : ℕ) (t : Fin m → ℕ) :
    Measurable (shiftedPathCoordinates X n t) := by
  -- Proof comment: each tuple coordinate is the measurable slice `X (t i + n)`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [shiftedPathCoordinates] using hX_meas (n + t i)

/-- Helper for Theorem 20.29: every Nat-indexed path measure is the projective limit of its
finite restriction marginals. -/
lemma natPathMeasure_isProjectiveLimit_restrictions
    (ν : Measure (ℕ → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset ℕ ↦ ν.map J.restrict) := by
  -- Proof comment: the projective-limit compatibility is exactly the defining restriction
  -- pushforward.
  intro J
  rfl

/-- Helper for Theorem 20.29: reindexing the sorted tuple attached to `J.orderEmbOfFin` recovers
the ordinary finite restriction map. -/
lemma piCongrLeft_orderEmbOfFin_eq_restrict
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

/-- Helper for Theorem 20.29: reindexing the ordered shifted coordinates by `J.orderEmbOfFin`
matches the usual finite restriction event. -/
lemma shiftedPathIndicator_eq_restrictIndicator
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

/-- Helper for Theorem 20.29: evaluating a composed kernel on a restricted pushforward equals the
corresponding set integral of row masses. -/
lemma kernelCompRestrictMapRealEqSetIntegral
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

/-- Helper for Theorem 20.29: evaluating a Nat-indexed path measure on a finite restriction
preimage is the same as evaluating its pushforward along that restriction. -/
lemma kernelReal_restrictPreimage_eq_mapRestrictReal
    (ν : Measure (ℕ → E)) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ν.real (J.restrict ⁻¹' A) = ((ν.map J.restrict).real A) := by
  -- Proof comment: this is the standard `map_measureReal_apply` rewrite for the measurable
  -- restriction map `J.restrict`.
  simpa using
    (MeasureTheory.map_measureReal_apply (μ := ν) (f := J.restrict)
      (Finset.measurable_restrict J) hA).symm

/-- Helper for Theorem 20.29: integrating the ordered-tuple indicator of a finite restriction
event against a Nat-indexed path measure recovers the corresponding restricted pushforward mass. -/
lemma orderedTupleIndicatorIntegral_eq_mapRestrictReal
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

/-- Helper for Theorem 20.29: transport the Chapter 17 ordered-coordinate conditional-expectation
formula from the natural-number submonoid of `NNReal` back to the discrete-time `ℕ` indexing
used in this file. -/
lemma orderedFutureCoordinateCondExp_of_markovProcessNat
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

/-- Helper for Theorem 20.29: Theorem 17.9 gives the conditional law of every finite shifted
future restriction on a history event. -/
lemma futurePathRestrictionIndicator_condExp
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
    -- Route correction: instead of asking Theorem 17.9 to elaborate directly at `ℕ`, first
    -- transport the ordered-coordinate statement through the natural-number submonoid of
    -- `NNReal`, then rewrite back to the local `shiftedPathCoordinates` spelling.
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

/-- Helper for Theorem 20.29: on each history event, the restricted shifted-future law agrees
with the path kernel mixed against the present-state law. -/
lemma restrictedFuturePathLaw_eq_mixedPathLaw_on_history
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
      -- Proof comment: apply the finite-restriction conditional-law formula on the history
      -- sigma-algebra.
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
                  (μ := μ.restrict B)
                  (f := fun ω ↦ J.restrict (shiftedPath X n ω))
                  ((Finset.measurable_restrict J).comp (measurable_shiftedPath X hX_meas n))
                  hA)
        _ = μ.real (futureEvent ∩ B) := by
              simpa [futureEvent] using
                (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B)
                  (t := futureEvent) hfuture_meas)
        _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
              simpa [futureEvent, Set.inter_comm] using hmass
    have hright_real :
        (((ρB.map J.restrict).real A)) = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
      have hmapJ :
          ρB.map J.restrict = κJ ∘ₘ ((μ.restrict B).map (X n)) := by
        dsimp [ρB, κJ]
        simpa using Measure.map_comp (((μ.restrict B).map (X n))) κ (Finset.measurable_restrict J)
      calc
        (((ρB.map J.restrict).real A))
            = ((κJ ∘ₘ ((μ.restrict B).map (X n))).real A) := by rw [hmapJ]
        _ = ∫ ω in B, (κJ (X n ω)).real A ∂μ := by
              simpa [κJ] using
                (kernelCompRestrictMapRealEqSetIntegral
                  (κ := κJ) (μ := μ) (hY := hX_meas n) hB_ambient hA)
        _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hrow : κJ (X n ω) = (κ (X n ω)).map J.restrict := by
                simpa [κJ] using Kernel.map_apply κ (Finset.measurable_restrict J) (X n ω)
              exact congrArg (fun ν : Measure (J → E) ↦ ν.real A) hrow
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map J.restrict) (ν := ρB.map J.restrict) (s := A) (t := A)).mp
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
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ'

/-- Helper for Theorem 20.29: the discrete-time Markov owner gives the full deterministic-time
conditional-expectation formula for bounded shifted future-path functionals. -/
lemma futurePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (n : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (shiftedPath X n ω) | generatedFiltrationSpace X n]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, g y ∂κ (X n ω) := by
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  let μ : Measure Ω := (P x : Measure Ω)
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X n]
    exact (measurable_pastPath X hX_meas n).comap_le
  have hfuture_meas : Measurable (shiftedPath X n) := measurable_shiftedPath X hX_meas n
  have hg_int :
      Integrable (fun ω ↦ g (shiftedPath X n ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    -- Proof comment: bounded measurable path observables are integrable under the start law.
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨shiftedPath X n ω, rfl⟩
  have hXn_generated : Measurable[generatedFiltrationSpace X n] (X n) := by
    -- Proof comment: the present state is the last coordinate of the finite history map.
    rw [generatedFiltrationSpace_eq_pastPath_comap X n]
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X n) inferInstance]
          (fun ω ↦ pastPath X n ω (Fin.last n)) := by
      exact (measurable_pi_apply (Fin.last n)).comp (comap_measurable (pastPath X n))
    simpa [pastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    -- Proof comment: integrating a measurable real-valued path functional against the path kernel
    -- is measurable in the starting state.
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X n] fun ω ↦ ∫ y, g y ∂κ (X n ω) := by
    exact hKernelIntegral_meas.comp hXn_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X n ω) := by
    exact hKernelIntegral_meas.comp (hX_meas n)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :=
    MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        -- Proof comment: the kernel-integral candidate stays bounded on each history event, so
        -- it is integrable there.
        refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hbound_row :
            ‖∫ y, g y ∂κ (X n ω)‖ ≤ C := by
          have hgC : ∀ᵐ y ∂κ (X n ω), ‖g y‖ ≤ C := by
            exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X n ω)) hgC)
        exact hbound_row)
      (fun s hs hμs ↦ by
        -- Proof comment: on each history event, rewrite both sides as integrals of `g` against
        -- the same shifted-future path law.
        let νB : Measure (ℕ → E) := (μ.restrict s).map (shiftedPath X n)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X n))
        have hs_history : MeasurableSet[generatedFiltrationSpace X n] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedFuturePathLaw_eq_mixedPathLaw_on_history X P κ hX_meas hX0 hpath x n
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
            ∫ ω in s, g (shiftedPath X n ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (shiftedPath X n ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (shiftedPath X n) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hg_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, g y ∂ρB = ∫ ω in s, ∫ y, g y ∂κ (X n ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict s).map (X n))
          have hcomp :
              (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, g y ∂ρB = ∫ y, g y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, g y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ₀) (a := ())
                      hg_ρB_int)
            _ = ∫ z, ∫ y, g y ∂κ z ∂((μ.restrict s).map (X n)) := by
                  simp [κ₀]
            _ = ∫ ω in s, ∫ y, g y ∂κ (X n ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas n).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable
  exact hCondExp.symm


/-- Helper for Theorem 20.29: the path-kernel row mass of a measurable event depends measurably on
the starting state. -/
lemma realizationPathKernel_real_measurable
    {B : Set (Stream' E)} (hB : MeasurableSet B) :
    Measurable fun y : E ↦ (realizationPathKernel (p := p) P X y).real B := by
  have hrowIntegral_meas :
      Measurable fun y : E ↦
        ∫ ξ, Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
          ∂(realizationPathKernel (p := p) P X y) := by
    exact
      ((Measurable.indicator measurable_const hB).stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun y : E ↦
          ∫ ξ, Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
            ∂(realizationPathKernel (p := p) P X y)).measurable
  -- Proof comment: rewrite the row mass as the integral of the event indicator.
  simpa [MeasureTheory.integral_indicator_one, hB] using hrowIntegral_meas

/-- Helper for Theorem 20.29: under `P x`, the initial state is almost surely `x`, rewritten in
the source-facing singleton-event form needed by the path-kernel API. -/
lemma realizationPathKernel_initialState_prob_eq_one
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] (x : E) :
    (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: evaluate the time-zero marginal identity on the singleton `{x}`.
  have hInit :=
    congrArg (fun μ : Measure E ↦ μ ({x} : Set E)) (hReal.initial_eq x)
  simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit

/-- Helper for Theorem 20.29: the time-`n` marginal of the realized path-law kernel is exactly
the original `n`-step transition row. -/
lemma realizationPathKernel_transition
    (x : E) (n : ℕ) :
    transitionKernel (realizationPathKernel (p := p) P X) n x = (discreteMatrixKernel p ^ n) x := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  -- Proof comment: push the path-law kernel forward to coordinate `n` and then reuse the
  -- realization identity for the time-`n` marginal.
  rw [transitionKernel_apply]
  change
    Measure.map (fun y : Stream' E ↦ y n)
      (Measure.map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω) (P x : Measure Ω)) =
        (discreteMatrixKernel p ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · exact measurable_stationaryTrajectoryMap p P X

/-- Helper for Theorem 20.29: the realized path-law kernel upgrades the realization to a
time-homogeneous Markov process on path space. -/
lemma realizationPathKernel_isTimeHomogeneousMarkovProcess :
    IsTimeHomogeneousMarkovProcess X P (realizationPathKernel (p := p) P X) := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := realizationPathKernel_initialState_prob_eq_one (p := p) (P := P) (X := X)
      path_law := ?_
      markov_property := ?_ }
  · intro x
    rfl
  · intro x A hA s t
    -- Proof comment: rewrite the owner-side path-kernel marginal back to the original transition
    -- semigroup before invoking the existing realization Markov property.
    refine (hReal.markov_property x hA s t).trans ?_
    filter_upwards with ω
    rw [realizationPathKernel_transition (p := p) (P := P) (X := X) (x := X s ω) t]

/-- Helper for Theorem 20.29: the deterministic-time conditional expectation of a future-path
indicator is the realized path-kernel mass started from the present state. -/
-- TODO: specialize `futurePathCondExp_of_markovProcessNat` to the indicator of `B`, then rewrite
-- the resulting kernel integral as the row mass `(realizationPathKernel ... (X n ω)).real B`.
lemma futurePathIndicator_condexp_eq_realizationPathKernel
    {B : Set (Stream' E)} (hB : MeasurableSet B) (x : E) (n : ℕ) :
    ((P x : Measure Ω)[fun ω ↦
        Set.indicator B (fun _ ↦ (1 : ℝ)) (fun k : ℕ ↦ X (n + k) ω)
      | generatedFiltrationSpace X n]) =ᵐ[(P x : Measure Ω)]
        fun ω ↦ (realizationPathKernel (p := p) P X (X n ω)).real B := by
  let hReal :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  let g : (ℕ → E) → ℝ := Set.indicator B (fun _ ↦ (1 : ℝ))
  have hg_meas : Measurable g := by
    -- Proof comment: the shifted future-path test function is the measurable indicator of the
    -- measurable event `B`.
    exact Measurable.indicator measurable_const hB
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    -- Proof comment: an indicator takes only the values `0` and `1`, so its range is bounded.
    simpa [g] using isBounded_range_indicator_one B
  -- Route correction: rather than importing the broken Chapter 17 Nat wrapper, use the local
  -- `shiftedPath` bridge proved above and specialize it directly to the realization path kernel.
  letI : IsTimeHomogeneousMarkovProcess X P (realizationPathKernel (p := p) P X) :=
    realizationPathKernel_isTimeHomogeneousMarkovProcess (p := p) (P := P) (X := X)
  have hAE :=
    futurePathCondExp_of_markovProcessNat
      (X := X) (P := P) (κ := realizationPathKernel (p := p) P X)
      (hX_meas := hReal.measurable_process)
      (hX0 := realizationPathKernel_initialState_prob_eq_one (p := p) (P := P) (X := X))
      (hpath := realizationPathKernel_apply (p := p) (P := P) (X := X))
      x n g hg_meas hg_bdd
  -- Proof comment: rewrite the generic kernel integral of the indicator to the corresponding row
  -- mass of the realization path kernel.
  filter_upwards [hAE] with ω hω
  calc
    ((P x : Measure Ω)[fun ω ↦
        Set.indicator B (fun _ ↦ (1 : ℝ)) (fun k : ℕ ↦ X (n + k) ω)
      | generatedFiltrationSpace X n]) ω
        = ((P x : Measure Ω)[fun ω ↦ g (shiftedPath X n ω) | generatedFiltrationSpace X n]) ω := by
            rfl
    _ = ∫ y, g y ∂(realizationPathKernel (p := p) P X (X n ω)) := hω
    _ = (realizationPathKernel (p := p) P X (X n ω)).real B := by
          simpa [g] using
            (MeasureTheory.integral_indicator_one
              (μ := realizationPathKernel (p := p) P X (X n ω)) (s := B) hB)


/-- Helper for Theorem 20.29: integrating a measurable state observable against the time-`n`
realization law is the same as integrating against the `n`-step transition row. -/
lemma realizedRowMass_integral_comp_transition_eq
    {g : E → ℝ} (hg : Measurable g) (x : E) (n : ℕ) :
    ∫ ω, g (X n ω) ∂(P x : Measure Ω) = ∫ z, g z ∂((discreteMatrixKernel p ^ n) x) := by
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  -- Proof comment: replace the time-`n` pushforward law of `X` under `P x` with the stored
  -- transition identity, then push the observable through the map.
  rw [← hReal.transition_eq x n, integral_map]
  · exact (hReal.measurable_process n).aemeasurable
  · exact hg.aestronglyMeasurable

/-- Helper for Theorem 20.29: the stationary path law is the path-law kernel mixed against the
invariant initial law `π`. -/
lemma stationaryProcessPathLaw_eq_comp_realizationPathKernel
    (P : E → ProbabilityMeasure Ω) (X : ℕ → Ω → E)
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (π : ProbabilityMeasure E) :
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) =
      realizationPathKernel (p := p) P X ∘ₘ (π : Measure E) := by
  let κpath : Kernel E (Stream' E) := realizationPathKernel (p := p) P X
  ext B hB
  -- Proof comment: expand the stationary mixture `P_π` state-by-state and identify each row
  -- pushforward with the corresponding row of the path-law kernel.
  calc
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) B
        = stationaryLaw P π ((fun ω : Ω ↦ fun n : ℕ ↦ X n ω) ⁻¹' B) := by
            exact
              stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
                (P := P) (X := X) (p := p) π hB
    _ = ∑' x : E, (((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))
          ((fun ω : Ω ↦ fun n : ℕ ↦ X n ω) ⁻¹' B) := by
            rw [stationaryLaw_eq_sum, Measure.sum_apply _ ((measurable_stationaryTrajectoryMap p P X) hB)]
    _ = ∑' x : E, (((π : Measure E) ({x} : Set E)) • κpath x) B := by
          refine tsum_congr fun x ↦ ?_
          rw [Measure.smul_apply, Measure.smul_apply]
          congr 1
          simpa [κpath] using
            (Measure.map_apply (μ := (P x : Measure Ω))
              (f := fun ω : Ω ↦ fun n : ℕ ↦ X n ω)
              (measurable_stationaryTrajectoryMap p P X) hB).symm
    _ = (κpath ∘ₘ (π : Measure E)) B := by
          rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ hB]

/-- Helper for Theorem 20.29: under the stationary mixture law, a history event at time `N`
paired with a future-path event integrates the realized path-kernel row mass over that history
event. -/
lemma stationaryLaw_historyEvent_futurePath_apply_eq_setIntegral_pathKernel
    {π : ProbabilityMeasure E} {N : ℕ} {AΩ : Set Ω}
    (hAΩ : MeasurableSet[generatedFiltrationSpace X N] AΩ)
    {C : Set (Stream' E)} (hC : MeasurableSet C) :
    (stationaryLaw P π).real (AΩ ∩ (shiftedPath X N) ⁻¹' C) =
      ∫ ω in AΩ, (realizationPathKernel (p := p) P X (X N ω)).real C ∂stationaryLaw P π := by
  let μ : Measure Ω := stationaryLaw P π
  let futureEvent : Set Ω := (shiftedPath X N) ⁻¹' C
  let rowMass : Ω → ℝ := fun ω ↦ (realizationPathKernel (p := p) P X (X N ω)).real C
  let leftIndicator : Ω → ℝ := Set.indicator (AΩ ∩ futureEvent) (fun _ ↦ (1 : ℝ))
  let rightIndicator : Ω → ℝ := Set.indicator AΩ rowMass
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hgenerated_le : generatedFiltrationSpace X N ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X N]
    exact (measurable_pastPath X hReal.measurable_process N).comap_le
  have hAΩ_ambient : MeasurableSet AΩ := hgenerated_le AΩ hAΩ
  have hfuture_meas : MeasurableSet futureEvent := by
    -- Proof comment: the future event is the preimage of `C` along the measurable shifted-path map.
    simpa [futureEvent] using (measurable_shiftedPath X hReal.measurable_process N) hC
  have hrowMass_meas : Measurable rowMass := by
    -- Proof comment: row masses of measurable path events vary measurably with the current state.
    exact
      (realizationPathKernel_real_measurable (p := p) (P := P) (X := X) hC).comp
        (hReal.measurable_process N)
  have hrowMass_bound : ∀ ω : Ω, ‖rowMass ω‖ ≤ 1 := by
    intro ω
    have hnonneg : 0 ≤ rowMass ω := MeasureTheory.measureReal_nonneg
    have hle : rowMass ω ≤ 1 := by
      simpa [rowMass] using
        (MeasureTheory.measureReal_le_one
          (μ := realizationPathKernel (p := p) P X (X N ω)) (s := C))
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hrowMass_int {ν : Measure Ω} [IsFiniteMeasure ν] : Integrable rowMass ν := by
    -- Proof comment: the row-mass observable is bounded by `1`, so it is integrable under every
    -- finite measure appearing in this stationary-law calculation.
    refine Integrable.of_bound hrowMass_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall hrowMass_bound
  have hleftIndicator_int_μ : Integrable leftIndicator μ := by
    simpa [leftIndicator] using
      (integrable_const (1 : ℝ)).indicator (hAΩ_ambient.inter hfuture_meas)
  have hrightIndicator_int_μ : Integrable rightIndicator μ := by
    simpa [rightIndicator] using (hrowMass_int (ν := μ)).indicator hAΩ_ambient
  have hterm :
      ∀ x : E,
        ∫ ω, leftIndicator ω ∂(P x : Measure Ω) =
          ∫ ω, rightIndicator ω ∂(P x : Measure Ω) := by
    intro x
    let μx : Measure Ω := (P x : Measure Ω)
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μx := by
      simpa [futureEvent] using (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmass :
        μx.real (AΩ ∩ futureEvent) = ∫ ω in AΩ, rowMass ω ∂μx := by
      have hcond :
          μx[fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω
              | generatedFiltrationSpace X N] =ᵐ[μx]
            rowMass := by
        -- Proof comment: specialize the future-path conditional-expectation bridge at the start
        -- state `x` and rewrite it into the local `rowMass` notation.
        simpa [futureEvent, rowMass] using
          futurePathIndicator_condexp_eq_realizationPathKernel
            (p := p) (P := P) (X := X) hC x N
      calc
        μx.real (AΩ ∩ futureEvent)
            = ∫ ω in AΩ,
                (μx[fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω
                  | generatedFiltrationSpace X N]) ω ∂μx := by
                  rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hAΩ,
                    ← MeasureTheory.integral_indicator hAΩ_ambient]
                  simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                    (MeasureTheory.integral_indicator_const
                      (μ := μx) (1 : ℝ) (hAΩ_ambient.inter hfuture_meas)).symm
        _ = ∫ ω in AΩ, rowMass ω ∂μx := by
              exact MeasureTheory.integral_congr_ae hcond.restrict
    -- Proof comment: rewrite both sides as indicator integrals under the start law `P x`.
    calc
      ∫ ω, leftIndicator ω ∂(P x : Measure Ω)
          = μx.real (AΩ ∩ futureEvent) := by
              simpa [leftIndicator] using
                (MeasureTheory.integral_indicator_one
                  (μ := μx) (s := AΩ ∩ futureEvent)
                  (hAΩ_ambient.inter hfuture_meas))
      _ = ∫ ω in AΩ, rowMass ω ∂μx := hmass
      _ = ∫ ω, rightIndicator ω ∂(P x : Measure Ω) := by
            symm
            simpa [rightIndicator] using
              (MeasureTheory.integral_indicator
                (μ := μx) (f := rowMass) hAΩ_ambient)
  -- Proof comment: expand the stationary mixture state-by-state and use the already-proved
  -- start-law identity on each summand.
  calc
    (stationaryLaw P π).real (AΩ ∩ futureEvent) = ∫ ω, leftIndicator ω ∂μ := by
        symm
        simpa [μ, leftIndicator] using
          (MeasureTheory.integral_indicator_one
            (μ := μ) (s := AΩ ∩ futureEvent) (hAΩ_ambient.inter hfuture_meas))
    _ =
        ∫ ω, leftIndicator ω
          ∂(Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω)) := by
            rw [← stationaryLaw_eq_sum (P := P) (π := π)]
    _ =
        ∑' x : E,
          ∫ ω, leftIndicator ω ∂((((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))) := by
            simpa [μ, stationaryLaw_eq_sum (P := P) (π := π)] using
              (MeasureTheory.integral_sum_measure
                (μ := fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))
                (f := leftIndicator)
                (by simpa [μ, stationaryLaw_eq_sum (P := P) (π := π)] using hleftIndicator_int_μ))
    _ =
        ∑' x : E,
          ((π : Measure E) ({x} : Set E)).toReal *
            ∫ ω, leftIndicator ω ∂(P x : Measure Ω) := by
              refine tsum_congr fun x ↦ ?_
              simpa [smul_eq_mul] using
                (MeasureTheory.integral_smul_measure
                  (f := leftIndicator) (((π : Measure E) ({x} : Set E))) (μ := (P x : Measure Ω)))
    _ =
        ∑' x : E,
          ((π : Measure E) ({x} : Set E)).toReal *
            ∫ ω, rightIndicator ω ∂(P x : Measure Ω) := by
              refine tsum_congr fun x ↦ ?_
              rw [hterm x]
    _ =
        ∑' x : E,
          ∫ ω, rightIndicator ω ∂((((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))) := by
              refine tsum_congr fun x ↦ ?_
              symm
              simpa [smul_eq_mul] using
                (MeasureTheory.integral_smul_measure
                  (f := rightIndicator) (((π : Measure E) ({x} : Set E))) (μ := (P x : Measure Ω)))
    _ =
        ∫ ω, rightIndicator ω
          ∂(Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω)) := by
            symm
            simpa [μ, stationaryLaw_eq_sum (P := P) (π := π)] using
              (MeasureTheory.integral_sum_measure
                (μ := fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))
                (f := rightIndicator)
                (by simpa [μ, stationaryLaw_eq_sum (P := P) (π := π)] using
                  hrightIndicator_int_μ))
    _ = ∫ ω, rightIndicator ω ∂μ := by
          simpa [μ, stationaryLaw_eq_sum (P := P) (π := π)]
    _ = ∫ ω in AΩ, rowMass ω ∂μ := by
          simpa [μ, rightIndicator] using
            (MeasureTheory.integral_indicator (μ := μ) (f := rowMass) hAΩ_ambient)

/-- Helper for Theorem 20.29: future-path event probabilities are kernel averages of the realized
path-law masses. -/
-- TODO: integrate `futurePathIndicator_condexp_eq_realizationPathKernel`, identify the left-hand
-- side with the future event mass, and rewrite the right-hand side through the time-`n` marginal
-- `markovRealization_integral_comp_transition_eq`.
lemma futurePathEvent_real_eq_kernelAverage
    {B : Set (Stream' E)} (hB : MeasurableSet B) (x : E) (n : ℕ) :
    (P x : Measure Ω).real ((fun ω : Ω ↦ fun k : ℕ ↦ X (n + k) ω) ⁻¹' B) =
      ∫ y, (realizationPathKernel (p := p) P X y).real B
        ∂((discreteMatrixKernel p ^ n) x) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let futureEvent : Set Ω := (fun ω : Ω ↦ fun k : ℕ ↦ X (n + k) ω) ⁻¹' B
  let g : E → ℝ := fun y ↦ (realizationPathKernel (p := p) P X y).real B
  have hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  have hfuture_meas : MeasurableSet futureEvent := by
    -- Proof comment: the shifted future event is the preimage of `B` along the measurable
    -- shifted-path map.
    simpa [futureEvent] using (measurable_shiftedPath X hReal.measurable_process n) hB
  have hIndicatorInt :
      Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ := by
    -- Proof comment: an indicator of a measurable event is integrable under the probability law
    -- `P x`.
    exact (integrable_const (1 : ℝ)).indicator hfuture_meas
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    -- Proof comment: the deterministic-time history sigma-algebra sits inside the ambient one
    -- because each coordinate of `X` is measurable.
    rw [generatedFiltrationSpace_eq_pastPath_comap X n]
    exact (measurable_pastPath X hReal.measurable_process n).comap_le
  have hg_meas : Measurable g := by
    -- Proof comment: row masses of measurable path events vary measurably with the start state.
    exact realizationPathKernel_real_measurable (p := p) (P := P) (X := X) hB
  let futureCondExp : Ω → ℝ :=
    MeasureTheory.condExp (m := generatedFiltrationSpace X n) μ
      (fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω)
  calc
    μ.real futureEvent
        = ∫ ω, Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            symm
            simpa [futureEvent] using
              (MeasureTheory.integral_indicator_one (μ := μ) (s := futureEvent) hfuture_meas)
    _ = ∫ ω, futureCondExp ω ∂μ := by
            symm
            exact
              integral_condExp
                (μ := μ)
                (m := generatedFiltrationSpace X n)
                (f := fun ω ↦ Set.indicator futureEvent (fun _ ↦ (1 : ℝ)) ω)
                hgenerated_le
    _ = ∫ ω, g (X n ω) ∂μ := by
          refine MeasureTheory.integral_congr_ae ?_
          simpa [futureEvent, g] using
            futurePathIndicator_condexp_eq_realizationPathKernel
              (p := p) (P := P) (X := X) hB x n
    _ = ∫ y, g y ∂((discreteMatrixKernel p ^ n) x) := by
          simpa [μ, g] using
            realizedRowMass_integral_comp_transition_eq
              (p := p) (P := P) (X := X) (g := g) hg_meas x n

/-- Helper for Theorem 20.29: the row mass of a shifted path event under
`realizationPathKernel` is the state-kernel average of the unshifted row masses. -/
lemma realizationPathKernel_iterateTail_real_eq_kernelAverage
    {B : Set (Stream' E)} (hB : MeasurableSet B) (x : E) (n : ℕ) :
    (realizationPathKernel (p := p) P X x).real ((Stream'.tail^[n]) ⁻¹' B) =
      ∫ y, (realizationPathKernel (p := p) P X y).real B
        ∂((discreteMatrixKernel p ^ n) x) := by
  -- Proof comment: first rewrite the tail event under the path-kernel pushforward as the
  -- corresponding shifted-path event under `P x`.
  calc
    (realizationPathKernel (p := p) P X x).real ((Stream'.tail^[n]) ⁻¹' B)
        = (P x : Measure Ω).real
            ((fun ω : Ω ↦ fun k : ℕ ↦ X k ω) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)) := by
              simpa [realizationPathKernel_apply] using
                (MeasureTheory.map_measureReal_apply
                  (μ := (P x : Measure Ω))
                  (f := fun ω : Ω ↦ fun k : ℕ ↦ X k ω)
                  (measurable_stationaryTrajectoryMap p P X)
                  ((measurable_tail (E := E)).iterate n hB))
    _ = (P x : Measure Ω).real ((fun ω : Ω ↦ fun k : ℕ ↦ X (n + k) ω) ⁻¹' B) := by
          congr 1
          exact trajectoryPreimage_iterateTail_eq_futurePathPreimage (X := X) (n := n) (B := B)
    _ = ∫ y, (realizationPathKernel (p := p) P X y).real B
          ∂((discreteMatrixKernel p ^ n) x) := by
            exact futurePathEvent_real_eq_kernelAverage
              (p := p) (P := P) (X := X) hB x n

/-- Helper for Theorem 20.29: the stationary path law is invariant under the one-sided shift. -/
-- TODO: rewrite `Measure.map Stream'.tail` by
-- `stationaryProcessPathLaw_iterateTail_apply_eq_stationaryLaw_futurePathPreimage`, apply
-- `futurePathEvent_real_eq_kernelAverage` at time `1`, and collapse the outer integral with the
-- invariance relation `hπ.def`.
lemma stationaryProcessPathLaw_map_tail_eq_self
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) :
    Measure.map Stream'.tail
      (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) =
        stationaryProcessPathLaw (p := p) P X π := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  ext B hB
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  let rowMass : E → ℝ := fun y ↦ (realizationPathKernel (p := p) P X y).real B
  have hrowMass_meas : Measurable rowMass := by
    -- Proof comment: measurable path events give measurable row masses in the starting state.
    exact realizationPathKernel_real_measurable (p := p) (P := P) (X := X) hB
  have hrowMass_nonneg : 0 ≤ᵐ[(π : Measure E)] rowMass :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hrowMass_int_pi : Integrable rowMass (π : Measure E) := by
    -- Proof comment: the row-mass observable is bounded by `1`, hence integrable under `π`.
    refine Integrable.of_bound hrowMass_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y ↦ by
      have hnonneg : 0 ≤ rowMass y := MeasureTheory.measureReal_nonneg
      have hle : rowMass y ≤ 1 := by
        simpa [rowMass] using
          (MeasureTheory.measureReal_le_one
            (μ := realizationPathKernel (p := p) P X y) (s := B))
      simpa [Real.norm_of_nonneg hnonneg] using hle
  have hright_real :
      Q.real B = ∫ y, rowMass y ∂(π : Measure E) := by
    -- Proof comment: unfold the stationary path law as the path-kernel mixture against `π`.
    calc
      Q.real B = ((realizationPathKernel (p := p) P X) ∘ₘ (π : Measure E)).real B := by
          rw [← stationaryProcessPathLaw_eq_comp_realizationPathKernel
            (P := P) (X := X) (p := p) π]
      _ = ∫ y, rowMass y ∂(π : Measure E) := by
          rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hB
            (ProbabilityTheory.Kernel.aemeasurable _)]
          have hlintegral :
              ∫⁻ y, realizationPathKernel (p := p) P X y B ∂(π : Measure E) =
                ENNReal.ofReal (∫ y, rowMass y ∂(π : Measure E)) := by
            calc
              ∫⁻ y, realizationPathKernel (p := p) P X y B ∂(π : Measure E)
                  = ∫⁻ y, ENNReal.ofReal (rowMass y) ∂(π : Measure E) := by
                      refine lintegral_congr_ae ?_
                      filter_upwards with y
                      change
                        realizationPathKernel (p := p) P X y B =
                          ENNReal.ofReal
                            ((realizationPathKernel (p := p) P X y).real B)
                      rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
                      exact measure_ne_top _ _
              _ = ENNReal.ofReal (∫ y, rowMass y ∂(π : Measure E)) := by
                    symm
                    exact
                      MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                        hrowMass_int_pi hrowMass_nonneg
          rw [hlintegral, ENNReal.toReal_ofReal]
          exact integral_nonneg_of_ae hrowMass_nonneg
  have hleft_real :
      (Measure.map Stream'.tail Q).real B = ∫ y, rowMass y ∂(π : Measure E) := by
    have hX1Law : Measure.map (X 1) (stationaryLaw P π) = (π : Measure E) := by
      ext s hs
      -- Proof comment: expand the stationary start law, identify the one-step marginal on each
      -- start state, and then collapse back with the invariance relation `hπ`.
      calc
        Measure.map (X 1) (stationaryLaw P π) s
            = stationaryLaw P π (X 1 ⁻¹' s) := by
                rw [Measure.map_apply (hReal.measurable_process 1) hs]
        _ =
            ∑' x : E, (((π : Measure E) ({x} : Set E)) • (P x : Measure Ω)) (X 1 ⁻¹' s) := by
              rw [stationaryLaw_eq_sum, Measure.sum_apply _ ((hReal.measurable_process 1) hs)]
        _ =
            ∑' x : E, (((π : Measure E) ({x} : Set E)) • (discreteMatrixKernel p x)) s := by
              refine tsum_congr fun x ↦ ?_
              have htransition :=
                congrArg (fun ν : Measure E ↦ ν s) (hReal.transition_eq x 1)
              rw [Measure.smul_apply]
              exact congrArg (((π : Measure E) ({x} : Set E)) * ·) <| by
                simpa [Measure.map_apply (hReal.measurable_process 1) hs] using htransition
        _ = ((discreteMatrixKernel p) ∘ₘ (π : Measure E)) s := by
              rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ hs]
        _ = (π : Measure E) s := by
              exact congrArg (fun ν : Measure E ↦ ν s) hπ.def
    -- Proof comment: rewrite the shifted path-law mass as a stationary history/future event with
    -- trivial history, then collapse the time-`1` marginal back to `π`.
    calc
      (Measure.map Stream'.tail Q).real B = Q.real (Stream'.tail ⁻¹' B) := by
          simpa [Q] using
            (MeasureTheory.map_measureReal_apply
              (μ := Q) (f := Stream'.tail) (measurable_tail (E := E)) hB)
      _ = (stationaryLaw P π).real ((shiftedPath X 1) ⁻¹' B) := by
            exact congrArg ENNReal.toReal
              (stationaryProcessPathLaw_iterateTail_apply_eq_stationaryLaw_futurePathPreimage
                (P := P) (X := X) (p := p) π 1 hB)
      _ =
          ∫ ω in (Set.univ : Set Ω), rowMass (X 1 ω) ∂stationaryLaw P π := by
            simpa [rowMass] using
              stationaryLaw_historyEvent_futurePath_apply_eq_setIntegral_pathKernel
                (P := P) (X := X) (p := p) (π := π) (N := 1)
                (AΩ := (Set.univ : Set Ω)) MeasurableSet.univ hB
      _ = ∫ ω, rowMass (X 1 ω) ∂stationaryLaw P π := by simp
      _ = ∫ y, rowMass y ∂(π : Measure E) := by
            calc
              ∫ ω, rowMass (X 1 ω) ∂stationaryLaw P π
                  = ∫ y, rowMass y ∂(Measure.map (X 1) (stationaryLaw P π)) := by
                      symm
                      exact
                        MeasureTheory.integral_map (hReal.measurable_process 1).aemeasurable
                          hrowMass_meas.aestronglyMeasurable
              _ = ∫ y, rowMass y ∂(π : Measure E) := by
                    rw [hX1Law]
  -- Proof comment: equality of the real masses on every measurable event gives equality of the
  -- finite measures.
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := Measure.map Stream'.tail Q) (ν := Q) (s := B) (t := B)).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Theorem 20.29: a shift-invariant path event induces a harmonic state observable via
the realized path-law kernel. -/
lemma shiftInvariantEvent_pathKernel_isHarmonic
    {A : Set (Stream' E)} (hA : MeasurableSet A) (hshiftA : Stream'.tail ⁻¹' A = A) :
    IsHarmonic (discreteMatrixKernel p)
      (fun x : E ↦ (realizationPathKernel (p := p) P X x).real A) := by
  let hp : IsStochasticMatrix p := stochasticMatrix_of_markovProcessRealization (p := p) P X
  letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  let f : E → ℝ := fun x : E ↦ (realizationPathKernel (p := p) P X x).real A
  have hf_bound : ∀ x : E, ‖f x‖ ≤ 1 := by
    intro x
    have hnonneg : 0 ≤ f x := MeasureTheory.measureReal_nonneg
    have hle : f x ≤ 1 := by
      simpa [f] using
        (MeasureTheory.measureReal_le_one
          (μ := realizationPathKernel (p := p) P X x) (s := A))
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hf_int : ∀ x : E, Integrable f ((discreteMatrixKernel p) x) := by
    intro x
    -- Proof comment: the path-event row mass is bounded by `1`, so it is integrable against each
    -- one-step row of the transition kernel.
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun y ↦ hf_bound y
  have htail_one : (Stream'.tail^[1]) ⁻¹' A = A := by
    simpa using hshiftA
  have hmean : ∀ x : E, f x = ∫ y, f y ∂((discreteMatrixKernel p) x) := by
    intro x
    have hleft :
        (realizationPathKernel (p := p) P X x).real ((Stream'.tail^[1]) ⁻¹' A) = f x := by
      simpa [f] using
        congrArg
          (fun s : Set (Stream' E) =>
            (realizationPathKernel (p := p) P X x).real s)
          htail_one
    -- Proof comment: one-step shift invariance turns the tail-preimage mass back into the
    -- original event mass, and the iterate-tail kernel identity then gives the harmonic average.
    calc
      f x = (realizationPathKernel (p := p) P X x).real ((Stream'.tail^[1]) ⁻¹' A) := hleft.symm
      _ = ∫ y, (realizationPathKernel (p := p) P X y).real A
            ∂((discreteMatrixKernel p ^ 1) x) := by
              exact realizationPathKernel_iterateTail_real_eq_kernelAverage
                (p := p) (P := P) (X := X) hA x 1
      _ = ∫ y, f y ∂((discreteMatrixKernel p) x) := by
            simpa [f]
  exact ⟨hf_int, hmean⟩

/-- Helper for Theorem 20.29: an invariant distribution for `discreteMatrixKernel p` is
automatically invariant for every kernel power. -/
lemma stationaryDistribution_invariant_pow
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) :
    ∀ n : ℕ, Kernel.Invariant (discreteMatrixKernel p ^ n) (π : Measure E) := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the zeroth kernel power is the identity kernel, so every measure is
      -- invariant at time `0`.
      simpa using (show Kernel.Invariant (Kernel.id : Kernel E E) (π : Measure E) from by
        change (Kernel.id : Kernel E E) ∘ₘ (π : Measure E) = (π : Measure E)
        exact MeasureTheory.Measure.id_comp (μ := (π : Measure E)))
  | succ n ihn =>
      -- Proof comment: compose the one-step invariance with the already-known `n`-step
      -- invariance.
      simpa [pow_succ'] using Kernel.Invariant.comp hπ ihn

/-- Helper for Theorem 20.29: every stochastic matrix on a countable discrete space has the
canonical `Kernel.trajMeasure` realization on path space. -/
private theorem existsCanonicalDiscreteMatrixRealization
    {S : Type*} [MeasurableSpace S] [DiscreteMeasurableSpace S] [Countable S]
    (q : S → S → ℝ≥0∞) (hq : IsStochasticMatrix q) :
    ∃ P : S → ProbabilityMeasure (ℕ → S),
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel q ^ n) P Function.eval := by
  let κ : Kernel S S := discreteMatrixKernel q
  letI : IsMarkovKernel κ := discreteMatrixKernel_isMarkovKernel q hq
  let η : (n : ℕ) → Kernel (Π i : Finset.Iic n, S) S :=
    fun n ↦
      Kernel.comap κ
        (fun z : Π i : Finset.Iic n, S ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (by fun_prop)
  have hη : ∀ n : ℕ, IsMarkovKernel (η n) := by
    intro n
    dsimp [η]
    infer_instance
  let μ : S → Measure (ℕ → S) :=
    fun x ↦
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      Kernel.trajMeasure (X := fun _ : ℕ ↦ S) (Measure.dirac x) η
  have hμ : ∀ x : S, IsProbabilityMeasure (μ x) := by
    intro x
    dsimp [μ]
    infer_instance
  let P : S → ProbabilityMeasure (ℕ → S) := fun x ↦ ⟨μ x, hμ x⟩
  refine ⟨P, ?_⟩
  refine ProbabilityTheory.isMarkovProcessRealization_of_oneStepKernel
    (κ₁ := κ)
    (P := P)
    (X := Function.eval)
    (hmeas := fun n ↦ measurable_pi_apply n)
    ?_ ?_
  · intro x
    have hprefix :
        (μ x).map (Preorder.frestrictLe 0) = Measure.dirac (fun _ : Finset.Iic 0 ↦ x) := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      -- Proof comment: the zeroth finite prefix of the trajectory measure is the deterministic
      -- singleton history at the start state `x`.
      simpa [μ, η, Kernel.partialTraj_self] using
        (Kernel.trajMeasure_map_frestrictLe
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) 0)
    -- Proof comment: composing the zeroth-prefix map with the coordinate projection recovers the
    -- initial Dirac law at time `0`.
    calc
      (P x : Measure (ℕ → S)).map (Function.eval 0)
          = ((μ x).map (Preorder.frestrictLe 0)).map
              (fun z : Finset.Iic 0 → S ↦ z ⟨0, Finset.mem_Iic.2 le_rfl⟩) := by
                rw [Measure.map_map (by fun_prop) (by fun_prop)]
                rfl
      _ = Measure.dirac x := by
            rw [hprefix]
            simp
  · intro x A hA s
    letI : Nonempty S := ⟨x⟩
    let H : (ℕ → S) → Finset.Iic s → S := Preorder.frestrictLe s
    have hH_meas : Measurable H := Preorder.measurable_frestrictLe s
    have hnext_meas : Measurable (Function.eval (s + 1) : (ℕ → S) → S) :=
      measurable_pi_apply (s + 1)
    have hcond :
        condDistrib (Function.eval (s + 1)) H (μ x) =ᵐ[(μ x).map H] η s := by
      letI : ∀ n : ℕ, IsMarkovKernel (η n) := hη
      -- Proof comment: `Kernel.trajMeasure` stores the canonical one-step conditional law of the
      -- coordinate process in terms of the kernel family `η`.
      simpa [μ, H, η] using
        (Kernel.condDistrib_trajMeasure
          (X := fun _ : ℕ ↦ S) (μ₀ := Measure.dirac x) (κ := η) (a := s))
    have hcondexp :
        (μ x)⟦(Function.eval (s + 1)) ⁻¹' A | MeasurableSpace.comap H inferInstance⟧ =ᵐ[μ x]
          fun ξ ↦ (condDistrib (Function.eval (s + 1)) H (μ x) (H ξ)).real A := by
      simpa using
        (condDistrib_ae_eq_condExp (μ := μ x) (X := H) (Y := Function.eval (s + 1))
          hH_meas hnext_meas hA).symm
    have hcond_comp :
        (fun ξ ↦ (condDistrib (Function.eval (s + 1)) H (μ x) (H ξ)).real A) =ᵐ[μ x]
          fun ξ ↦ (η s (H ξ)).real A := by
      filter_upwards [ae_eq_comp hH_meas.aemeasurable hcond] with ξ hξ
      simpa [Function.comp] using congrArg (fun ν : Measure S ↦ ν.real A) hξ
    have hgen :
        generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) s =
          MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance := by
      refine le_antisymm ?_ ?_
      · rw [generatedFiltrationSpace]
        refine iSup₂_le fun t ht ↦ ?_
        let i : Finset.Iic s := ⟨t, Finset.mem_Iic.2 ht⟩
        have hCoord :
            Measurable[
              MeasurableSpace.comap (Preorder.frestrictLe s) inferInstance]
              (Function.eval t : (ℕ → S) → S) := by
          simpa [Function.eval, Preorder.frestrictLe_apply, i] using
            (measurable_pi_apply i).comp (comap_measurable (Preorder.frestrictLe s))
        exact hCoord.comap_le
      · have hPrefix :
          Measurable[
            generatedFiltrationSpace (Function.eval : ℕ → (ℕ → S) → S) s]
            (Preorder.frestrictLe s : (ℕ → S) → Finset.Iic s → S) := by
          rw [@measurable_pi_iff]
          intro i
          refine Measurable.of_comap_le ?_
          exact le_iSup_of_le i.1 <| le_iSup_of_le (Finset.mem_Iic.1 i.2) le_rfl
        exact hPrefix.comap_le
    -- Proof comment: after identifying the finite-history sigma-algebra with the prefix pullback,
    -- the canonical conditional law becomes exactly the one-step Markov property.
    rw [hgen]
    exact hcondexp.trans <|
      hcond_comp.trans <|
        Filter.Eventually.of_forall fun ξ ↦ by
          simpa [η, H, Preorder.frestrictLe_apply] using
            congrArg (fun ν : Measure S ↦ ν.real A) rfl

/-- Helper for Theorem 20.29: irreducibility, aperiodicity, and an invariant distribution force
the Dirac-started `n`-step laws of `p` to converge to `π` in total variation. -/
lemma nStepLaw_tendsto_invariantDistribution_of_irreducible_aperiodic
    [IsMarkovKernel (discreteMatrixKernel p)] (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    (haper : IsAperiodic (discreteMatrixKernel p))
    (x : E) :
    Tendsto
      (fun n : ℕ ↦ totalVariationDistance (nStepLaw p (diracProba x) n) π)
      atTop (𝓝 0) := by
  let hp : IsStochasticMatrix p := stochasticMatrix_of_markovProcessRealization (p := p) P X
  letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  letI : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) :=
    discreteMatrixKernel_isIrreducible_of_irreducibleMarkovChain
      (P := P) (X := X) (p := p) hirr
  have hcoupling : HasSuccessfulCoupling p := by
    refine ⟨?_⟩
    rcases existsCanonicalDiscreteMatrixRealization
        (q := independentCoalescentMatrix p)
        (hq := independentCoalescentMatrix_isStochasticMatrix p hp) with
      ⟨Pq, hqreal⟩
    -- Proof comment: Theorem 18.11 upgrades the canonical coalescent realization to a successful
    -- coupling once irreducibility, an invariant distribution, and aperiodicity are available.
    exact ⟨(ℕ → E × E), inferInstance, Pq, Function.eval,
      independentCoalescentChain_isSuccessfulMarkovCoupling
        (p := p) (P := Pq) (Z := Function.eval) (hinv := ⟨π, hπ⟩) haper hqreal⟩
  have hπ_nStep : ∀ n : ℕ, nStepLaw p π n = π := by
    intro n
    ext A hA
    -- Proof comment: invariance of `π` under every kernel power identifies the evolved law with
    -- the original invariant distribution at each time `n`.
    exact congrArg (fun μ : Measure E ↦ μ A)
      (stationaryDistribution_invariant_pow (p := p) hπ n).def
  have hconv :
      Tendsto
        (fun n : ℕ ↦ totalVariationDistance (nStepLaw p (diracProba x) n) (nStepLaw p π n))
        atTop (𝓝 0) := by
    exact nStepTotalVariationDistance_tendsto_zero_of_hasSuccessfulCoupling
      (p := p) hcoupling (diracProba x) π
  -- Proof comment: Theorem 18.12 gives convergence against every second initial law; for the
  -- invariant law `π`, the second trajectory is constant in `n`.
  simpa [hπ_nStep] using hconv

/-- Helper for Theorem 20.29: under the stationary mixture law `P_π`, every time marginal `X n`
still has law `π`. -/
lemma stationaryLaw_map_process_eq_invariant
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E)) :
    ∀ n : ℕ, Measure.map (X n) (stationaryLaw P π) = (π : Measure E) := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  intro n
  have hπn :
      Kernel.Invariant (discreteMatrixKernel p ^ n) (π : Measure E) :=
    stationaryDistribution_invariant_pow (p := p) hπ n
  ext A hA
  -- Proof comment: expand the stationary mixture `P_π`, rewrite each row through the
  -- time-`n` marginal identity, and then collapse back to the invariant measure of the
  -- `n`-step kernel.
  calc
    Measure.map (X n) (stationaryLaw P π) A
        = stationaryLaw P π (X n ⁻¹' A) := by
            rw [Measure.map_apply (hReal.measurable_process n) hA]
    _ =
        ∑' x : E, (((π : Measure E) ({x} : Set E)) • (P x : Measure Ω)) (X n ⁻¹' A) := by
          rw [stationaryLaw_eq_sum, Measure.sum_apply _ ((hReal.measurable_process n) hA)]
    _ =
        ∑' x : E, (((π : Measure E) ({x} : Set E)) • ((discreteMatrixKernel p ^ n) x)) A := by
          refine tsum_congr fun x ↦ ?_
          have htransition :
              (P x : Measure Ω) (X n ⁻¹' A) = ((discreteMatrixKernel p ^ n) x) A := by
            -- Proof comment: evaluate the time-`n` marginal identity on the measurable set `A`.
            simpa [Measure.map_apply (hReal.measurable_process n) hA] using
              congrArg (fun μ : Measure E ↦ μ A) (hReal.transition_eq x n)
          rw [Measure.smul_apply]
          exact congrArg (((π : Measure E) ({x} : Set E)) * ·) htransition
    _ = ((discreteMatrixKernel p ^ n) ∘ₘ (π : Measure E)) A := by
          rw [Measure.comp_eq_sum_of_countable, Measure.sum_apply _ hA]
    _ = (π : Measure E) A := by
          exact congrArg (fun μ : Measure E ↦ μ A) hπn.def

/-- Helper for Theorem 20.29: every coordinate of the stationary path law has marginal `π`. -/
lemma stationaryProcessPathLaw_map_coordinate_eq_invariant
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    (n : ℕ) :
    Measure.map (Function.eval n : Stream' E → E)
      (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) =
        (π : Measure E) := by
  -- Proof comment: factor the coordinate projection through the trajectory map and reuse the
  -- stationary marginal identity for `stationaryLaw P π`.
  calc
    Measure.map (Function.eval n : Stream' E → E)
        (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
        =
          Measure.map ((Function.eval n : Stream' E → E) ∘
            (fun ω : Ω ↦ fun k : ℕ ↦ X k ω)) (stationaryLaw P π) := by
              rw [stationaryProcessPathLaw_def (p := p) P X π]
              rw [Measure.map_map
                (μ := stationaryLaw P π)
                (f := fun ω : Ω ↦ fun k : ℕ ↦ X k ω)
                (g := (Function.eval n : Stream' E → E))]
              · exact (measurable_pi_apply n : Measurable (Function.eval n : Stream' E → E))
              · exact measurable_stationaryTrajectoryMap p P X
    _ = Measure.map (X n) (stationaryLaw P π) := by
          rfl
    _ = (π : Measure E) := stationaryLaw_map_process_eq_invariant (P := P) (X := X) (p := p) hπ n

/-- Helper for Theorem 20.29: composing a kernel with the Dirac probability at `x` recovers the
row measure `κ x`. -/
lemma kernelComp_diracProba_eq_row
    (κ : Kernel E E) (x : E) :
    κ ∘ₘ (diracProba x : Measure E) = κ x := by
  ext s hs
  -- Proof comment: evaluate the composed measure on a measurable set and collapse the outer
  -- Dirac integral immediately.
  rw [MeasureTheory.Measure.comp_eq_comp_const_apply]
  rw [Kernel.comp_apply' _ _ _ hs]
  rw [Kernel.const_apply]
  change ∫⁻ b, (κ b) s ∂(Measure.dirac x) = (κ x) s
  rw [lintegral_dirac' x (κ.measurable_coe hs)]

/-- Helper for Theorem 20.29: the integral gap of a bounded measurable real test function is
controlled by twice the total-variation distance. -/
lemma integral_sub_abs_le_two_mul_totalVariationDistance
    (μ ν : ProbabilityMeasure E) {f : E → ℝ}
    (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    |∫ x, f x ∂(μ : Measure E) - ∫ x, f x ∂(ν : Measure E)| ≤
      2 * totalVariationDistance μ ν := by
  let S : Set ℝ := {r : ℝ | ∃ g : E → ℝ,
    Measurable g ∧
      (∀ x, ‖g x‖ ≤ 1) ∧
      r = ∫ x, g x ∂(μ : Measure E) - ∫ x, g x ∂(ν : Measure E)}
  have hS_bddAbove : BddAbove S := by
    refine ⟨2, ?_⟩
    intro r hr
    rcases hr with ⟨g, hg_meas, hg_bound, rfl⟩
    have hμ_norm :
        ‖∫ x, g x ∂(μ : Measure E)‖ ≤ 1 := by
      simpa using
        (norm_integral_le_of_norm_le_const
          (μ := (μ : Measure E)) (C := 1) (ae_of_all _ hg_bound))
    have hν_norm :
        ‖∫ x, g x ∂(ν : Measure E)‖ ≤ 1 := by
      simpa using
        (norm_integral_le_of_norm_le_const
          (μ := (ν : Measure E)) (C := 1) (ae_of_all _ hg_bound))
    have hμ_bounds :
        -1 ≤ ∫ x, g x ∂(μ : Measure E) ∧ ∫ x, g x ∂(μ : Measure E) ≤ 1 := by
      exact abs_le.mp (by simpa using hμ_norm)
    have hν_bounds :
        -1 ≤ ∫ x, g x ∂(ν : Measure E) ∧ ∫ x, g x ∂(ν : Measure E) ≤ 1 := by
      exact abs_le.mp (by simpa using hν_norm)
    linarith
  have hupper :
      ∀ {g : E → ℝ}, Measurable g → (∀ x, ‖g x‖ ≤ 1) →
        ∫ x, g x ∂(μ : Measure E) - ∫ x, g x ∂(ν : Measure E) ≤
          2 * totalVariationDistance μ ν := by
    intro g hg_meas hg_bound
    have hmem :
        ∫ x, g x ∂(μ : Measure E) - ∫ x, g x ∂(ν : Measure E) ∈ S :=
      ⟨g, hg_meas, hg_bound, rfl⟩
    have hsSup_ge :
        ∫ x, g x ∂(μ : Measure E) - ∫ x, g x ∂(ν : Measure E) ≤ sSup S :=
      le_csSup hS_bddAbove hmem
    rw [totalVariationDistance_eq_sSup_bounded_measurable]
    linarith
  have hup :
      ∫ x, f x ∂(μ : Measure E) - ∫ x, f x ∂(ν : Measure E) ≤
        2 * totalVariationDistance μ ν :=
    hupper hf_meas hf_bound
  have hlow :
      -(∫ x, f x ∂(μ : Measure E) - ∫ x, f x ∂(ν : Measure E)) ≤
        2 * totalVariationDistance μ ν := by
    simpa [integral_neg, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hupper (g := fun x ↦ -f x) hf_meas.neg (fun x ↦ by simpa using hf_bound x)
  have hleft :
      -(2 * totalVariationDistance μ ν) ≤
        ∫ x, f x ∂(μ : Measure E) - ∫ x, f x ∂(ν : Measure E) := by
    linarith
  exact abs_le.2 ⟨hleft, hup⟩

/-- Helper for Theorem 20.29: the stationary path-law correlation of the zero-coordinate singleton
event `{ω | ω 0 = x}` with its `n`-step shift is exactly the invariant singleton mass times the
`n`-step self-return mass at `x`. -/
lemma zeroCoordinateSingletonCorrelation_eq_invariantMass_mul_stepMass
    {π : ProbabilityMeasure E} (x : E) (n : ℕ) :
    let Ax : Set (Stream' E) := {ω | ω 0 = x}
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
      (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax) =
        π {x} * ((discreteMatrixKernel p ^ n) x) ({x} : Set E) := by
  classical
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  let Ax : Set (Stream' E) := {ω | ω 0 = x}
  let AΩ : Set Ω := X 0 ⁻¹' ({x} : Set E)
  let BΩ : Set Ω := X n ⁻¹' ({x} : Set E)
  have hX0_meas : Measurable (X 0) := hReal.measurable_process 0
  have hXn_meas : Measurable (X n) := hReal.measurable_process n
  have hAΩ_meas : MeasurableSet AΩ := hX0_meas (measurableSet_singleton x)
  have hBΩ_meas : MeasurableSet BΩ := hXn_meas (measurableSet_singleton x)
  have hAx_meas : MeasurableSet Ax := by
    -- Proof comment: the zero-coordinate singleton event is the preimage of `{x}` under `eval 0`.
    change MeasurableSet ((Function.eval 0 : Stream' E → E) ⁻¹' ({x} : Set E))
    exact (measurable_pi_apply 0 : Measurable (Function.eval 0 : Stream' E → E))
      (measurableSet_singleton x)
  have hAx_preimage :
      (fun ω : Ω ↦ fun k : ℕ ↦ X k ω) ⁻¹' (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax) = AΩ ∩ BΩ := by
    -- Proof comment: on the pushed-forward trajectory, membership in the shifted singleton event
    -- is exactly the state event `X n = x`.
    ext ω
    constructor
    · rintro ⟨h0, hn⟩
      refine ⟨?_, ?_⟩
      · simpa [Ax, AΩ] using h0
      · change (Stream'.tail^[n]) (fun k : ℕ ↦ X k ω) 0 = x at hn
        simpa [BΩ, Function.eval] using
          (show X n ω = x by
            simpa [Function.eval] using
              (tailIterate_apply (E := E) n (fun k : ℕ ↦ X k ω) 0).symm.trans hn)
    · rintro ⟨h0, hn⟩
      refine ⟨?_, ?_⟩
      · simpa [Ax, AΩ] using h0
      · change (Stream'.tail^[n]) (fun k : ℕ ↦ X k ω) 0 = x
        simpa [Function.eval] using
          (tailIterate_apply (E := E) n (fun k : ℕ ↦ X k ω) 0).trans hn
  have hPx0 :
      (P x : Measure Ω) AΩ = 1 := by
    have hInit :=
      congrArg (fun μ : Measure E ↦ μ ({x} : Set E)) (hReal.initial_eq x)
    simpa [AΩ, Measure.map_apply hX0_meas (measurableSet_singleton x)] using hInit
  have hPxc : (P x : Measure Ω) AΩᶜ = 0 := by
    -- Proof comment: under `P x`, the initial state is almost surely `x`, so the complement of
    -- `{X 0 = x}` is null.
    simpa [hPx0] using measure_compl (μ := (P x : Measure Ω)) hAΩ_meas
  have hterm :
      ∀ y : E,
        (P y : Measure Ω) (AΩ ∩ BΩ) =
          if y = x then ((discreteMatrixKernel p ^ n) x) ({x} : Set E) else 0 := by
    intro y
    by_cases hy : y = x
    · subst y
      have hdiff_zero : (P x : Measure Ω) (BΩ \ AΩ) = 0 :=
        measure_mono_null (fun ω hω ↦ hω.2) hPxc
      have hinter :
          (P x : Measure Ω) (AΩ ∩ BΩ) = (P x : Measure Ω) BΩ := by
        -- Proof comment: the null exceptional set `AΩᶜ` removes the `X 0 = x` constraint under
        -- the start law `P x`.
        have hsplit := measure_inter_add_diff (μ := (P x : Measure Ω)) BΩ hAΩ_meas
        have hsplit' : (P x : Measure Ω) (AΩ ∩ BΩ) + (P x : Measure Ω) (BΩ \ AΩ) =
            (P x : Measure Ω) BΩ := by
          simpa [Set.inter_comm] using hsplit
        rw [hdiff_zero, add_zero] at hsplit'
        exact hsplit'
      have htrans :=
        congrArg (fun μ : Measure E ↦ μ ({x} : Set E)) (hReal.transition_eq x n)
      have hBΩ_eq :
          (P x : Measure Ω) BΩ = ((discreteMatrixKernel p ^ n) x) ({x} : Set E) := by
        simpa [BΩ, Measure.map_apply hXn_meas (measurableSet_singleton x)] using htrans
      simpa using hinter.trans hBΩ_eq
    · have hAy :
          (P y : Measure Ω) AΩ = 0 := by
        have hInit :=
          congrArg (fun μ : Measure E ↦ μ ({x} : Set E)) (hReal.initial_eq y)
        simpa [AΩ, hy, Measure.map_apply hX0_meas (measurableSet_singleton x)] using hInit
      have hinter_zero : (P y : Measure Ω) (AΩ ∩ BΩ) = 0 :=
        measure_mono_null Set.inter_subset_left hAy
      simpa [hy] using hinter_zero
  -- Proof comment: expand the stationary law as the weighted sum over start states and collapse
  -- the sum to the single start state `x`.
  calc
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
        (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax)
        =
          stationaryLaw P π (AΩ ∩ BΩ) := by
            have hmap :
                (Measure.map (fun ω : Ω ↦ fun k : ℕ ↦ X k ω) (stationaryLaw P π))
                    (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax) =
                  stationaryLaw P π
                    ((fun ω : Ω ↦ fun k : ℕ ↦ X k ω) ⁻¹'
                      (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax)) := by
              exact Measure.map_apply (measurable_stationaryTrajectoryMap p P X)
                (hAx_meas.inter ((measurable_tail (E := E)).iterate n hAx_meas))
            simpa [stationaryProcessPathLaw_def (p := p) P X π, hAx_preimage] using hmap
    _ =
        ∑' y : E, (((π : Measure E) ({y} : Set E)) • (P y : Measure Ω)) (AΩ ∩ BΩ) := by
          rw [stationaryLaw_eq_sum, Measure.sum_apply _ (hAΩ_meas.inter hBΩ_meas)]
    _ =
        ∑' y : E,
          ((π : Measure E) ({y} : Set E)) *
            (if y = x then ((discreteMatrixKernel p ^ n) x) ({x} : Set E) else 0) := by
          refine tsum_congr fun y ↦ ?_
          rw [Measure.smul_apply]
          simp [hterm y]
    _ = π {x} * ((discreteMatrixKernel p ^ n) x) ({x} : Set E) := by
          rw [tsum_eq_single x]
          · simp
          · intro y hy
            simp [hy]

/-- Helper for Theorem 20.29: under the stationary mixture law, the joint singleton event
`{X₀ = x, Xₙ = y}` has mass `π{x} pⁿ(x,y)`. -/
lemma stationaryLaw_zeroTime_nTime_singleton_eq
    {π : ProbabilityMeasure E} (x y : E) (n : ℕ) :
    stationaryLaw P π (X 0 ⁻¹' ({x} : Set E) ∩ X n ⁻¹' ({y} : Set E)) =
      π {x} * ((discreteMatrixKernel p ^ n) x) ({y} : Set E) := by
  classical
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  let AΩ : Set Ω := X 0 ⁻¹' ({x} : Set E)
  let BΩ : Set Ω := X n ⁻¹' ({y} : Set E)
  have hAΩ_meas : MeasurableSet AΩ :=
    (hReal.measurable_process 0) (measurableSet_singleton x)
  have hBΩ_meas : MeasurableSet BΩ :=
    (hReal.measurable_process n) (measurableSet_singleton y)
  have hPx0 :
      (P x : Measure Ω) AΩ = 1 := by
    simpa [AΩ] using
      realizationPathKernel_initialState_prob_eq_one
        (p := p) (P := P) (X := X) x
  have hPxc : (P x : Measure Ω) AΩᶜ = 0 := by
    simpa [hPx0] using measure_compl (μ := (P x : Measure Ω)) hAΩ_meas
  have hterm :
      ∀ z : E,
        (P z : Measure Ω) (AΩ ∩ BΩ) =
          if z = x then ((discreteMatrixKernel p ^ n) x) ({y} : Set E) else 0 := by
    intro z
    by_cases hz : z = x
    · subst z
      have hdiff_zero : (P x : Measure Ω) (BΩ \ AΩ) = 0 :=
        measure_mono_null (fun ω hω ↦ hω.2) hPxc
      have hinter :
          (P x : Measure Ω) (AΩ ∩ BΩ) = (P x : Measure Ω) BΩ := by
        -- Proof comment: under `P x`, the null exceptional set `AΩᶜ` removes the initial-state
        -- constraint from the joint event.
        have hsplit := measure_inter_add_diff (μ := (P x : Measure Ω)) BΩ hAΩ_meas
        have hsplit' :
            (P x : Measure Ω) (AΩ ∩ BΩ) + (P x : Measure Ω) (BΩ \ AΩ) =
              (P x : Measure Ω) BΩ := by
          simpa [Set.inter_comm] using hsplit
        rw [hdiff_zero, add_zero] at hsplit'
        exact hsplit'
      have htrans :=
        congrArg (fun μ : Measure E ↦ μ ({y} : Set E)) (hReal.transition_eq x n)
      have hBΩ_eq :
          (P x : Measure Ω) BΩ = ((discreteMatrixKernel p ^ n) x) ({y} : Set E) := by
        simpa [BΩ, Measure.map_apply (hReal.measurable_process n) (measurableSet_singleton y)] using
          htrans
      simpa using hinter.trans hBΩ_eq
    · have hAz :
          (P z : Measure Ω) AΩ = 0 := by
        have hInit :=
          congrArg (fun μ : Measure E ↦ μ ({x} : Set E)) (hReal.initial_eq z)
        simpa [AΩ, hz, Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using
          hInit
      have hinter_zero : (P z : Measure Ω) (AΩ ∩ BΩ) = 0 :=
        measure_mono_null Set.inter_subset_left hAz
      simpa [hz] using hinter_zero
  -- Proof comment: expand the stationary law into the countable mixture over start states and
  -- collapse the sum to the single contributing start state `x`.
  calc
    stationaryLaw P π (AΩ ∩ BΩ)
        = ∑' z : E, (((π : Measure E) ({z} : Set E)) • (P z : Measure Ω)) (AΩ ∩ BΩ) := by
            rw [stationaryLaw_eq_sum, Measure.sum_apply _ (hAΩ_meas.inter hBΩ_meas)]
    _ =
        ∑' z : E,
          ((π : Measure E) ({z} : Set E)) *
            (if z = x then ((discreteMatrixKernel p ^ n) x) ({y} : Set E) else 0) := by
          refine tsum_congr fun z ↦ ?_
          rw [Measure.smul_apply]
          simp [hterm z]
    _ = π {x} * ((discreteMatrixKernel p ^ n) x) ({y} : Set E) := by
          rw [tsum_eq_single x]
          · simp
          · intro z hz
            simp [hz]

/-- Helper for Theorem 20.29: under the stationary law of an invariant distribution, every bounded
harmonic square moment agrees with the invariant square moment. -/
lemma stationaryLaw_harmonic_square_eq_invariant
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f)) (n : ℕ) :
    ∫ ω, (f (X n ω)) ^ 2 ∂stationaryLaw P π = ∫ z, (f z) ^ 2 ∂(π : Measure E) := by
  let μ : Measure Ω := stationaryLaw P π
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  obtain ⟨R, hR⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  have hf_bound : ∀ z : E, ‖f z‖ ≤ R := fun z ↦ hR _ ⟨z, rfl⟩
  have hf_sq_int_pi : Integrable (fun z : E ↦ (f z) ^ 2) (π : Measure E) := by
    -- Proof comment: boundedness of `f` gives integrability of its square under the invariant
    -- distribution.
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable (R ^ 2) ?_
    exact Filter.Eventually.of_forall fun z ↦ by
      have hz := hf_bound z
      have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg (f z)) hz
      simpa [pow_two, abs_mul] using
        mul_le_mul hz hz (norm_nonneg _) hR_nonneg
  -- Proof comment: rewrite the time-`n` square moment through the marginal law of `X n` and
  -- then use stationarity of that marginal.
  calc
    ∫ ω, (f (X n ω)) ^ 2 ∂μ
        = ∫ z, (f z) ^ 2 ∂(Measure.map (X n) μ) := by
            symm
            exact
              integral_map (hReal.measurable_process n).aemeasurable
                Measurable.of_discrete.aestronglyMeasurable
    _ = ∫ z, (f z) ^ 2 ∂(π : Measure E) := by
          rw [stationaryLaw_map_process_eq_invariant (P := P) (X := X) (p := p) hπ n]

/-- Helper for Theorem 20.29: under the stationary law, the harmonic cross moment at times `0`
and `n` equals the invariant square moment. -/
lemma stationaryLaw_harmonic_cross_eq_invariant
    {π : ProbabilityMeasure E}
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) (n : ℕ) :
    ∫ ω, f (X 0 ω) * f (X n ω) ∂stationaryLaw P π = ∫ z, (f z) ^ 2 ∂(π : Measure E) := by
  let μ : Measure Ω := stationaryLaw P π
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  obtain ⟨R, hR⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  have hf_bound : ∀ z : E, ‖f z‖ ≤ R := fun z ↦ hR _ ⟨z, rfl⟩
  have hf_sq_int_pi : Integrable (fun z : E ↦ (f z) ^ 2) (π : Measure E) := by
    -- Proof comment: the same boundedness estimate controls the square moment on the state
    -- space.
    refine Integrable.of_bound Measurable.of_discrete.aestronglyMeasurable (R ^ 2) ?_
    exact Filter.Eventually.of_forall fun z ↦ by
      have hz := hf_bound z
      have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg (f z)) hz
      simpa [pow_two, abs_mul] using
        mul_le_mul hz hz (norm_nonneg _) hR_nonneg
  let hprod : Ω → ℝ := fun ω ↦ f (X 0 ω) * f (X n ω)
  have hprod_int : Integrable hprod μ := by
    -- Proof comment: boundedness of `f` also controls the product moment under the stationary
    -- mixture law.
    refine Integrable.of_bound
      (((Measurable.of_discrete.comp (hReal.measurable_process 0)).mul
        (Measurable.of_discrete.comp (hReal.measurable_process n))).aestronglyMeasurable)
      (R * R) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg (f (X 0 ω))) (hf_bound _)
      calc
        ‖hprod ω‖ = ‖f (X 0 ω)‖ * ‖f (X n ω)‖ := by
          simpa [hprod] using abs_mul (f (X 0 ω)) (f (X n ω))
        _ ≤ R * R := by
          exact mul_le_mul (hf_bound _) (hf_bound _) (norm_nonneg _) hR_nonneg
  have hprod_sum :
      Integrable hprod
        (Measure.sum fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω)) := by
    simpa [μ, stationaryLaw_eq_sum (P := P) (π := π)] using hprod_int
  -- Proof comment: expand the stationary mixture state-by-state and use the harmonic
  -- expectation identity on each start state.
  calc
    ∫ ω, hprod ω ∂μ
        = ∫ ω, hprod ω ∂(Measure.sum fun x ↦
            ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω)) := by
              rw [show μ = stationaryLaw P π by rfl, stationaryLaw_eq_sum (P := P) (π := π)]
    _ = ∑' x : E, ∫ ω, hprod ω ∂((((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))) := by
          simpa using
            (MeasureTheory.integral_sum_measure
              (μ := fun x ↦ ((π : Measure E) ({x} : Set E)) • (P x : Measure Ω))
              (f := hprod) hprod_sum)
    _ = ∑' x : E, ((π : Measure E) ({x} : Set E)).toReal * ∫ ω, hprod ω ∂(P x : Measure Ω) := by
          refine tsum_congr fun x ↦ ?_
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_smul_measure (μ := (P x : Measure Ω)) (f := hprod)
              ((π : Measure E) ({x} : Set E)))
    _ = ∑' x : E, ((π : Measure E) ({x} : Set E)).toReal * (f x) ^ 2 := by
          refine tsum_congr fun x ↦ ?_
          have hstart_mem :
              X 0 ⁻¹' ({x} : Set E) ∈ ae (P x : Measure Ω) := by
            exact
              (mem_ae_iff_prob_eq_one
                ((hReal.measurable_process 0) (measurableSet_singleton x))).2
                (realizationPathKernel_initialState_prob_eq_one
                  (p := p) (P := P) (X := X) x)
          calc
            ((π : Measure E) ({x} : Set E)).toReal * ∫ ω, hprod ω ∂(P x : Measure Ω)
                = ((π : Measure E) ({x} : Set E)).toReal *
                    ∫ ω, f x * f (X n ω) ∂(P x : Measure Ω) := by
                      congr 1
                      refine integral_congr_ae ?_
                      filter_upwards [hstart_mem] with ω hω
                      have h0 : X 0 ω = x := by simpa using hω
                      simp [hprod, h0]
            _ = ((π : Measure E) ({x} : Set E)).toReal *
                  (f x * ∫ ω, f (X n ω) ∂(P x : Measure Ω)) := by
                    rw [integral_const_mul]
            _ = ((π : Measure E) ({x} : Set E)).toReal * (f x * f x) := by
                  rw [harmonicExpectation_eq_start_of_realization
                    (p := p) (P := P) (X := X) (f := f) hf_bdd hf_harmonic x n]
            _ = ((π : Measure E) ({x} : Set E)).toReal * (f x) ^ 2 := by ring
    _ = ∫ z, (f z) ^ 2 ∂(π : Measure E) := by
          symm
          simpa [hprod, smul_eq_mul] using
            (MeasureTheory.integral_countable (μ := (π : Measure E))
              (f := fun z : E ↦ (f z) ^ 2) hf_sq_int_pi)

/-- Helper for Theorem 20.29: under the stationary law of an invariant distribution, every bounded
harmonic observable takes the same value at times `0` and `n` almost surely. -/
lemma stationaryLaw_harmonic_process_ae_eq_initial
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    {f : E → ℝ} (hf_bdd : Bornology.IsBounded (Set.range f))
    (hf_harmonic : IsHarmonic (discreteMatrixKernel p) f) (n : ℕ) :
    (fun ω ↦ f (X n ω)) =ᵐ[stationaryLaw P π] fun ω ↦ f (X 0 ω) := by
  let μ : Measure Ω := stationaryLaw P π
  let hReal : IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X :=
    inferInstance
  obtain ⟨R, hR⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  have hf_bound : ∀ z : E, ‖f z‖ ≤ R := fun z ↦ hR _ ⟨z, rfl⟩
  have htime_sq_int : ∀ m : ℕ, Integrable (fun ω ↦ (f (X m ω)) ^ 2) μ := by
    intro m
    -- Proof comment: boundedness of `f` controls every square along the realization.
    refine Integrable.of_bound
      ((Measurable.of_discrete.comp (hReal.measurable_process m)).pow_const 2).aestronglyMeasurable
      (R ^ 2) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      have hz := hf_bound (X m ω)
      have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg (f (X m ω))) hz
      simpa [pow_two, abs_mul] using
        mul_le_mul hz hz (norm_nonneg _) hR_nonneg
  let hprod : Ω → ℝ := fun ω ↦ f (X 0 ω) * f (X n ω)
  have hprod_int : Integrable hprod μ := by
    -- Proof comment: the product term is bounded by the product of the uniform bounds.
    refine Integrable.of_bound
      (((Measurable.of_discrete.comp (hReal.measurable_process 0)).mul
        (Measurable.of_discrete.comp (hReal.measurable_process n))).aestronglyMeasurable)
      (R * R) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      have hR_nonneg : 0 ≤ R := le_trans (norm_nonneg (f (X 0 ω))) (hf_bound _)
      calc
        ‖hprod ω‖ = ‖f (X 0 ω)‖ * ‖f (X n ω)‖ := by
          simpa [hprod] using abs_mul (f (X 0 ω)) (f (X n ω))
        _ ≤ R * R := by
          exact mul_le_mul (hf_bound _) (hf_bound _) (norm_nonneg _) hR_nonneg
  let hdiffSq : Ω → ℝ := fun ω ↦ (f (X n ω) - f (X 0 ω)) ^ 2
  have hdiffSq_int : Integrable hdiffSq μ := by
    -- Proof comment: the squared difference is bounded by the square of the doubled uniform
    -- bound.
    have hdiffSq_measurable : Measurable hdiffSq := by
      exact
        (((Measurable.of_discrete.comp (hReal.measurable_process n)).sub
          (Measurable.of_discrete.comp (hReal.measurable_process 0))).pow_const 2)
    have hdiffSq_meas : AEStronglyMeasurable hdiffSq μ := by
      exact hdiffSq_measurable.aestronglyMeasurable
    refine Integrable.of_bound
      hdiffSq_meas
      ((2 * R) ^ 2) ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      have hω :
          ‖f (X n ω) - f (X 0 ω)‖ ≤ 2 * R := by
        calc
          ‖f (X n ω) - f (X 0 ω)‖ ≤ ‖f (X n ω)‖ + ‖f (X 0 ω)‖ := by
            simpa [sub_eq_add_neg] using norm_add_le (f (X n ω)) (-f (X 0 ω))
          _ ≤ R + R := add_le_add (hf_bound _) (hf_bound _)
          _ = 2 * R := by ring
      have hR_nonneg : 0 ≤ 2 * R := by
        nlinarith [norm_nonneg (f (X n ω) - f (X 0 ω)), hω]
      have hωsq :
          ‖f (X n ω) - f (X 0 ω)‖ * ‖f (X n ω) - f (X 0 ω)‖ ≤ (2 * R) * (2 * R) :=
        mul_le_mul hω hω (norm_nonneg _) hR_nonneg
      simpa [hdiffSq, pow_two, abs_mul] using hωsq
  have hdiffSq_nonneg :
      0 ≤ᵐ[μ] hdiffSq := Filter.Eventually.of_forall fun ω ↦ sq_nonneg _
  have hsum_sq_int :
      Integrable (fun ω ↦ (f (X n ω)) ^ 2 + (f (X 0 ω)) ^ 2) μ :=
    (htime_sq_int n).add (htime_sq_int 0)
  have hdiffSq_zero : ∫ ω, hdiffSq ω ∂μ = 0 := by
    -- Proof comment: expand the square and substitute the already isolated square and cross
    -- identities.
    calc
      ∫ ω, hdiffSq ω ∂μ
          = ∫ ω, ((f (X n ω)) ^ 2 + (f (X 0 ω)) ^ 2 - 2 * (f (X 0 ω) * f (X n ω))) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              ring
      _ = (∫ ω, (f (X n ω)) ^ 2 ∂μ + ∫ ω, (f (X 0 ω)) ^ 2 ∂μ) -
            ∫ ω, 2 * hprod ω ∂μ := by
              rw [integral_sub hsum_sq_int (hprod_int.const_mul 2)]
              rw [integral_add (htime_sq_int n) (htime_sq_int 0)]
      _ = (∫ z, (f z) ^ 2 ∂(π : Measure E) + ∫ z, (f z) ^ 2 ∂(π : Measure E)) -
            2 * ∫ ω, hprod ω ∂μ := by
              have hsqn :
                  ∫ ω, (f (X n ω)) ^ 2 ∂μ = ∫ z, (f z) ^ 2 ∂(π : Measure E) :=
                stationaryLaw_harmonic_square_eq_invariant
                  (P := P) (X := X) (p := p) hπ hf_bdd n
              have hsq0 :
                  ∫ ω, (f (X 0 ω)) ^ 2 ∂μ = ∫ z, (f z) ^ 2 ∂(π : Measure E) :=
                stationaryLaw_harmonic_square_eq_invariant
                  (P := P) (X := X) (p := p) hπ hf_bdd 0
              rw [integral_const_mul, hsqn, hsq0]
      _ = 0 := by
            rw [stationaryLaw_harmonic_cross_eq_invariant
              (P := P) (X := X) (p := p) (π := π) hf_bdd hf_harmonic n]
            ring_nf
  have hsq_ae :
      hdiffSq =ᵐ[μ] 0 := by
    exact
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hdiffSq_nonneg hdiffSq_int).1
        hdiffSq_zero
  filter_upwards [hsq_ae] with ω hω
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hω)

/-- Helper for Theorem 20.29: irreducibility forces the path-kernel mass of a shift-invariant
event to be constant in the starting state. -/
lemma shiftInvariantEvent_pathKernel_mass_constant
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    {A : Set (Stream' E)} (hA : MeasurableSet A) (hshiftA : Stream'.tail ⁻¹' A = A) :
    ∀ x y : E,
      (realizationPathKernel (p := p) P X x).real A =
        (realizationPathKernel (p := p) P X y).real A := by
  let f : E → ℝ := fun z : E ↦ (realizationPathKernel (p := p) P X z).real A
  have hf_harmonic :
      IsHarmonic (discreteMatrixKernel p) f :=
    shiftInvariantEvent_pathKernel_isHarmonic
      (P := P) (X := X) (p := p) hA hshiftA
  have hf_bdd : Bornology.IsBounded (Set.range f) := by
    have hIcc : Bornology.IsBounded (Set.Icc (0 : ℝ) 1) := Metric.isBounded_Icc 0 1
    refine hIcc.subset ?_
    rintro _ ⟨z, rfl⟩
    constructor
    · exact MeasureTheory.measureReal_nonneg
    · simpa [f] using
        (MeasureTheory.measureReal_le_one
          (μ := realizationPathKernel (p := p) P X z) (s := A))
  intro x y
  obtain ⟨n, hxy_pos⟩ :
      ∃ n : ℕ, 0 < ((discreteMatrixKernel p ^ n) x) ({y} : Set E) := by
    letI : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) :=
      discreteMatrixKernel_isIrreducible_of_irreducibleMarkovChain
        (P := P) (X := X) (p := p) hirr
    have hIrr : Kernel.IsIrreducible (Measure.count : Measure E) (discreteMatrixKernel p) :=
      inferInstance
    simpa using hIrr.irreducible (A := ({y} : Set E)) (MeasurableSet.singleton y) (by simp) x
  have hEqAE :
      (fun ω ↦ f (X n ω)) =ᵐ[stationaryLaw P π] fun ω ↦ f (X 0 ω) :=
    stationaryLaw_harmonic_process_ae_eq_initial
      (P := P) (X := X) (p := p) hπ hf_bdd hf_harmonic n
  let S : Set Ω := X 0 ⁻¹' ({x} : Set E) ∩ X n ⁻¹' ({y} : Set E)
  have hS_pos : 0 < stationaryLaw P π S := by
    -- Proof comment: irreducibility gives a positive `x → y` transition at some time, and the
    -- stationary singleton mass at `x` is strictly positive as well.
    have hπx_pos : 0 < π {x} :=
      invariantDistribution_apply_singleton_pos (P := P) (X := X) (p := p) hirr hπ x
    have hπx_pos' : 0 < ((π : Measure E) ({x} : Set E)) := by
      simpa [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
        (show 0 < ((π {x} : NNReal) : ℝ≥0∞) from by
          exact_mod_cast hπx_pos)
    rw [stationaryLaw_zeroTime_nTime_singleton_eq (P := P) (X := X) (p := p) (π := π) x y n]
    positivity
  by_contra hneq
  have hbad_zero :
      stationaryLaw P π {ω : Ω | f (X n ω) ≠ f (X 0 ω)} = 0 := by
    -- Proof comment: almost-everywhere equality is exactly the nullity of the disagreement set.
    simpa [Filter.EventuallyEq, ae_iff] using hEqAE
  have hsubset :
      S ⊆ {ω : Ω | f (X n ω) ≠ f (X 0 ω)} := by
    intro ω hω
    rcases hω with ⟨hx, hy⟩
    have hx0 : X 0 ω = x := by simpa using hx
    have hyn : X n ω = y := by simpa using hy
    have hneq' : f y ≠ f x := fun h => hneq h.symm
    simpa [S, f, hx0, hyn] using hneq'
  have hS_zero : stationaryLaw P π S = 0 :=
    measure_mono_null hsubset hbad_zero
  exact hS_pos.ne' hS_zero

/-- Helper for Theorem 20.29: a measurable shift-invariant event has the same path-kernel row mass
for every start state, hence equal to its stationary path-law mass. -/
lemma shiftInvariantEvent_pathKernel_value_eq_stationaryMass
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    {A : Set (Stream' E)} (hA : MeasurableSet A) (hshiftA : Stream'.tail ⁻¹' A = A) :
    ∀ x : E,
      (realizationPathKernel (p := p) P X x).real A =
        (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)).real A := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  intro x
  have hconst :
      ∀ y : E,
        (realizationPathKernel (p := p) P X y).real A =
          (realizationPathKernel (p := p) P X x).real A := by
    intro y
    exact
      (shiftInvariantEvent_pathKernel_mass_constant
        (P := P) (X := X) (p := p) hirr hπ hA hshiftA y x)
  have hQ :
      Q.real A = ∫ y, (realizationPathKernel (p := p) P X y).real A ∂(π : Measure E) := by
    rw [show Q = realizationPathKernel (p := p) P X ∘ₘ (π : Measure E) by
      simpa [Q] using
        stationaryProcessPathLaw_eq_comp_realizationPathKernel
          (P := P) (X := X) (p := p) π]
    simpa using
      (kernelCompRestrictMapRealEqSetIntegral
        (κ := realizationPathKernel (p := p) P X) (μ := (π : Measure E)) (Y := fun y : E ↦ y)
        (hY := measurable_id) (B := Set.univ) (A := A) MeasurableSet.univ hA)
  -- Proof comment: the harmonic argument already showed that every row mass agrees with the row
  -- started from `x`, so integrating against `π` leaves that common value unchanged.
  calc
    (realizationPathKernel (p := p) P X x).real A
        = ∫ y, (realizationPathKernel (p := p) P X x).real A ∂(π : Measure E) := by
            simp
    _ = ∫ y, (realizationPathKernel (p := p) P X y).real A ∂(π : Measure E) := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          exact (hconst y).symm
    _ = Q.real A := hQ.symm

/-- Helper for Theorem 20.29: a measurable shift-invariant event is independent of every finite
cylinder under the stationary path law. -/
lemma shiftInvariantEvent_cylinder_real_eq_product
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    {A : Set (Stream' E)} (hA : MeasurableSet A) (hshiftA : Stream'.tail ⁻¹' A = A)
    {s : Finset ℕ} {A0 : Set (s → E)} (hA0 : MeasurableSet A0) :
    let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
    let C : Set (Stream' E) := MeasureTheory.cylinder s A0
    Q.real (C ∩ A) = Q.real C * Q.real A := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  let C : Set (Stream' E) := MeasureTheory.cylinder s A0
  let traj : Ω → Stream' E := fun ω : Ω ↦ fun k : ℕ ↦ X k ω
  let N : ℕ := s.sup id
  let AΩ : Set Ω := traj ⁻¹' C
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hgenerated_le : generatedFiltrationSpace X N ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X N]
    exact (measurable_pastPath X hReal.measurable_process N).comap_le
  have hC : MeasurableSet C := by
    -- Proof comment: finite cylinders are measurable because they are finite-coordinate
    -- restriction preimages.
    simpa [C, MeasureTheory.cylinder] using hA0.preimage (Finset.measurable_restrict s)
  have hAΩ :
      MeasurableSet[generatedFiltrationSpace X N] AΩ := by
    -- Proof comment: the cylinder depends only on coordinates up to `N = s.sup id`.
    simpa [AΩ, C, traj, N] using
      cylinderTrajectoryPreimage_measurableInFiltration
        (X := X) (s := s) (A0 := A0) hA0
  have hAΩ_ambient : MeasurableSet AΩ := hgenerated_le AΩ hAΩ
  have hQC :
      Q.real C = (stationaryLaw P π).real AΩ := by
    -- Proof comment: unfold the stationary path law once to rewrite the cylinder mass as a
    -- stationary realization-law mass of the corresponding history event.
    simpa [Q, C, AΩ, traj] using
      congrArg ENNReal.toReal
        (stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
          (P := P) (X := X) (p := p) π (A := C) hC)
  have hshiftN : (Stream'.tail^[N]) ⁻¹' A = A := by
    -- Proof comment: a one-step invariant event is automatically invariant under every iterate of
    -- the shift.
    simpa [Set.preimage_iterate_eq] using
      (Function.IsFixedPt.preimage_iterate (f := Stream'.tail) hshiftA N)
  calc
    Q.real (C ∩ A)
        = (stationaryLaw P π).real (AΩ ∩ (shiftedPath X N) ⁻¹' A) := by
            have hCA : MeasurableSet (C ∩ A) := hC.inter hA
            calc
              Q.real (C ∩ A)
                  = (stationaryLaw P π).real (traj ⁻¹' (C ∩ A)) := by
                      simpa [Q, traj] using
                        congrArg ENNReal.toReal
                          (stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
                            (P := P) (X := X) (p := p) π (A := C ∩ A) hCA)
              _ = (stationaryLaw P π).real (AΩ ∩ (shiftedPath X N) ⁻¹' A) := by
                    congr 1
                    calc
                      traj ⁻¹' (C ∩ A) = traj ⁻¹' C ∩ traj ⁻¹' A := by
                        rw [Set.preimage_inter]
                      _ = AΩ ∩ traj ⁻¹' A := by
                            rfl
                      _ = AΩ ∩ traj ⁻¹' ((Stream'.tail^[N]) ⁻¹' A) := by
                            simpa using
                              congrArg (fun s : Set (Stream' E) ↦ AΩ ∩ traj ⁻¹' s) hshiftN.symm
                      _ = AΩ ∩ (shiftedPath X N) ⁻¹' A := by
                            simpa [traj] using
                              congrArg (fun s : Set Ω ↦ AΩ ∩ s)
                                (trajectoryPreimage_iterateTail_eq_futurePathPreimage
                                  (X := X) (n := N) (B := A))
    _ = ∫ ω in AΩ, (realizationPathKernel (p := p) P X (X N ω)).real A ∂stationaryLaw P π := by
          simpa using
            stationaryLaw_historyEvent_futurePath_apply_eq_setIntegral_pathKernel
              (P := P) (X := X) (p := p) (π := π) (N := N) (AΩ := AΩ) hAΩ hA
    _ = ∫ ω in AΩ, Q.real A ∂stationaryLaw P π := by
          -- Proof comment: irreducibility makes the path-kernel mass of the shift-invariant event
          -- constant in the present state, hence equal to the stationary path-law mass.
          refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
          simpa [Q] using
            shiftInvariantEvent_pathKernel_value_eq_stationaryMass
              (P := P) (X := X) (p := p) hirr hπ hA hshiftA (X N ω)
    _ = (stationaryLaw P π).real AΩ * Q.real A := by
          rw [← MeasureTheory.integral_indicator hAΩ_ambient]
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_indicator_const
              (μ := stationaryLaw P π) (Q.real A) hAΩ_ambient)
    _ = Q.real C * Q.real A := by
          rw [hQC]

/-- Helper for Theorem 20.29: if two event pairs are close in symmetric difference, then the
correlation error of the original pair is controlled by the approximant correlation error and the
two approximation masses. -/
lemma mixingErrorBound_ofSymmDiffApprox (P : Measure Ω) [IsProbabilityMeasure P]
    {A A' C C' : Set Ω}
    (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hC : MeasurableSet C) (hC' : MeasurableSet C') :
    abs (P.real (A ∩ C) - P.real A * P.real C) ≤
      abs (P.real (A' ∩ C') - P.real A' * P.real C') +
        (2 * P.real ((A \ A') ∪ (A' \ A)) +
          2 * P.real ((C \ C') ∪ (C' \ C))) := by
  have hInterSubsetA : (A ∩ C) ∆ (A' ∩ C) ⊆ A ∆ A' := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
    rcases hx with ⟨hxAC, hxA'C⟩ | ⟨hxA'C, hxAC⟩
    · by_cases hxA' : x ∈ A'
      · right
        refine ⟨hxA', ?_⟩
        intro hxA
        exact hxA'C ⟨hxA', hxAC.2⟩
      · exact Or.inl ⟨hxAC.1, hxA'⟩
    · by_cases hxA : x ∈ A
      · left
        refine ⟨hxA, ?_⟩
        intro hxA'
        exact hxAC ⟨hxA, hxA'C.2⟩
      · exact Or.inr ⟨hxA'C.1, hxA⟩
  have hInterSubsetC : (A' ∩ C) ∆ (A' ∩ C') ⊆ C ∆ C' := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
    rcases hx with ⟨hxA'C, hxA'C'⟩ | ⟨hxA'C', hxA'C⟩
    · by_cases hxC' : x ∈ C'
      · right
        refine ⟨hxC', ?_⟩
        intro hxC
        exact hxA'C' ⟨hxA'C.1, hxC'⟩
      · exact Or.inl ⟨hxA'C.2, hxC'⟩
    · by_cases hxC : x ∈ C
      · left
        refine ⟨hxC, ?_⟩
        intro hxC'
        exact hxA'C ⟨hxA'C'.1, hxC⟩
      · exact Or.inr ⟨hxA'C'.2, hxC⟩
  have hInterA :
      |P.real (A ∩ C) - P.real (A' ∩ C)| ≤ P.real (A ∆ A') := by
    -- Proof comment: first freeze the second event and only compare the first event.
    refine le_trans ?_ (measureReal_mono (μ := P) hInterSubsetA)
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := (hA.inter hC).nullMeasurableSet) (ht := (hA'.inter hC).nullMeasurableSet))
  have hInterC :
      |P.real (A' ∩ C) - P.real (A' ∩ C')| ≤ P.real (C ∆ C') := by
    -- Proof comment: then freeze the approximating first event and compare the second one.
    refine le_trans ?_ (measureReal_mono (μ := P) hInterSubsetC)
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := (hA'.inter hC).nullMeasurableSet) (ht := (hA'.inter hC').nullMeasurableSet))
  have hAErr :
      |P.real A - P.real A'| ≤ P.real (A ∆ A') := by
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := hA.nullMeasurableSet) (ht := hA'.nullMeasurableSet))
  have hCErr :
      |P.real C - P.real C'| ≤ P.real (C ∆ C') := by
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := hC.nullMeasurableSet) (ht := hC'.nullMeasurableSet))
  have hA_nonneg : 0 ≤ P.real A := by positivity
  have hA'_nonneg : 0 ≤ P.real A' := by positivity
  have hC_nonneg : 0 ≤ P.real C := by positivity
  have hC'_nonneg : 0 ≤ P.real C' := by positivity
  have hA_le_one : P.real A ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ A) : P.real A ≤ P.real Set.univ)
  have hA'_le_one : P.real A' ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ A') : P.real A' ≤ P.real Set.univ)
  have hC_le_one : P.real C ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ C) : P.real C ≤ P.real Set.univ)
  have hProdA :
      |P.real A * P.real C - P.real A' * P.real C| ≤ P.real (A ∆ A') := by
    have hmul :
        P.real A * P.real C - P.real A' * P.real C =
          (P.real A - P.real A') * P.real C := by
      ring
    calc
      |P.real A * P.real C - P.real A' * P.real C|
          = |P.real A - P.real A'| * P.real C := by
              rw [hmul, abs_mul, abs_of_nonneg hC_nonneg]
      _ ≤ |P.real A - P.real A'| * 1 := by
            gcongr
      _ = |P.real A - P.real A'| := by ring
      _ ≤ P.real (A ∆ A') := hAErr
  have hProdC :
      |P.real A' * P.real C - P.real A' * P.real C'| ≤ P.real (C ∆ C') := by
    have hmul :
        P.real A' * P.real C - P.real A' * P.real C' =
          P.real A' * (P.real C - P.real C') := by
      ring
    calc
      |P.real A' * P.real C - P.real A' * P.real C'|
          = P.real A' * |P.real C - P.real C'| := by
              rw [hmul, abs_mul, abs_of_nonneg hA'_nonneg]
      _ ≤ 1 * |P.real C - P.real C'| := by
            gcongr
      _ = |P.real C - P.real C'| := by ring
      _ ≤ P.real (C ∆ C') := hCErr
  have hInter :
      |P.real (A ∩ C) - P.real (A' ∩ C')|
        ≤ P.real (A ∆ A') + P.real (C ∆ C') := by
    calc
      |P.real (A ∩ C) - P.real (A' ∩ C')|
          ≤ |P.real (A ∩ C) - P.real (A' ∩ C)| +
              |P.real (A' ∩ C) - P.real (A' ∩ C')| := by
                simpa using
                  (abs_sub_le (P.real (A ∩ C)) (P.real (A' ∩ C)) (P.real (A' ∩ C')))
      _ ≤ P.real (A ∆ A') + P.real (C ∆ C') := add_le_add hInterA hInterC
  have hProd :
      |P.real A' * P.real C' - P.real A * P.real C|
        ≤ P.real (A ∆ A') + P.real (C ∆ C') := by
    calc
      |P.real A' * P.real C' - P.real A * P.real C|
          ≤ |P.real A' * P.real C' - P.real A' * P.real C| +
              |P.real A' * P.real C - P.real A * P.real C| := by
                simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using
                  (abs_sub_le (P.real A' * P.real C') (P.real A' * P.real C)
                    (P.real A * P.real C))
      _ ≤ P.real (C ∆ C') + P.real (A ∆ A') := by
            refine add_le_add ?_ ?_
            · simpa [abs_sub_comm] using hProdC
            · simpa [abs_sub_comm] using hProdA
      _ = P.real (A ∆ A') + P.real (C ∆ C') := by ring
  have hApproxCorr :
      |P.real (A' ∩ C') - P.real A * P.real C|
        ≤ |P.real (A' ∩ C') - P.real A' * P.real C'| +
            (P.real (A ∆ A') + P.real (C ∆ C')) := by
    calc
      |P.real (A' ∩ C') - P.real A * P.real C|
          ≤ |P.real (A' ∩ C') - P.real A' * P.real C'| +
              |P.real A' * P.real C' - P.real A * P.real C| := by
                simpa using
                  (abs_sub_le (P.real (A' ∩ C')) (P.real A' * P.real C')
                    (P.real A * P.real C))
      _ ≤ |P.real (A' ∩ C') - P.real A' * P.real C'| +
            (P.real (A ∆ A') + P.real (C ∆ C')) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hProd
                  (|P.real (A' ∩ C') - P.real A' * P.real C'|)
  -- Proof comment: combine the intersection error, the approximant correlation term, and the
  -- product error into a single triangle-inequality estimate.
  calc
    |P.real (A ∩ C) - P.real A * P.real C|
        ≤ |P.real (A ∩ C) - P.real (A' ∩ C')| +
            |P.real (A' ∩ C') - P.real A * P.real C| := by
              simpa using
                (abs_sub_le (P.real (A ∩ C)) (P.real (A' ∩ C')) (P.real A * P.real C))
    _ ≤ (P.real (A ∆ A') + P.real (C ∆ C')) +
          (|P.real (A' ∩ C') - P.real A' * P.real C'| +
            (P.real (A ∆ A') + P.real (C ∆ C'))) := by
              exact add_le_add hInter hApproxCorr
    _ = |P.real (A' ∩ C') - P.real A' * P.real C'| +
          2 * P.real (A ∆ A') + 2 * P.real (C ∆ C') := by
            ring
    _ = |P.real (A' ∩ C') - P.real A' * P.real C'| +
          (2 * P.real ((A \ A') ∪ (A' \ A)) +
            2 * P.real ((C \ C') ∪ (C' \ C))) := by
              simp [Set.symmDiff_def, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 20.29: the stationary path law makes the one-sided shift
`Stream'.tail` measure-preserving. -/
lemma stationary_shift_measurePreserving
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    MeasurePreserving
      Stream'.tail
      (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
      (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) := by
  -- Proof comment: measurability is canonical for `Stream'.tail`, and stationarity of the path
  -- law was already proved as equality of pushed-forward measures.
  refine ⟨measurable_tail (E := E), ?_⟩
  exact stationaryProcessPathLaw_map_tail_eq_self (P := P) (X := X) (p := p) hπ

/-- Helper for Theorem 20.29: every measurable shift-invariant event under the stationary path
law has mass `q` satisfying `q = q^2`. -/
lemma shiftInvariantEvent_real_eq_sq_of_irreducible_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure)
    {A : Set (Stream' E)} (hA : MeasurableSet A) (hshiftA : Stream'.tail ⁻¹' A = A) :
    let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
    Q.real A = Q.real A * Q.real A := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  have hdense : Q.MeasureDense (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) := by
    refine Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ := Q)
        (𝒜 := MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E))
        MeasureTheory.isSetAlgebra_measurableCylinders ?_
    simpa using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℕ ↦ E)).symm
  have hsmall :
      ∀ ε > 0,
        |Q.real A - Q.real A * Q.real A| < ε := by
    intro ε hε
    let δ : ℝ := ε / 2
    have hδ : 0 < δ := by positivity
    rcases hdense.fin_meas_approx hA (measure_ne_top Q A) δ hδ with
      ⟨Aε, hAε_mem, -, hAε_close⟩
    let sA : Finset ℕ := MeasureTheory.measurableCylinders.finset hAε_mem
    let SA : Set ((i : sA) → E) := MeasureTheory.measurableCylinders.set hAε_mem
    have hAε_eq : Aε = MeasureTheory.cylinder sA SA :=
      MeasureTheory.measurableCylinders.eq_cylinder hAε_mem
    have hAε : MeasurableSet Aε := MeasurableSet.of_mem_measurableCylinders hAε_mem
    have hSA : MeasurableSet SA := MeasureTheory.measurableCylinders.measurableSet hAε_mem
    have hAε_closeReal : Q.real (A ∆ Aε) < δ := by
      simpa [Measure.real_def, δ] using ENNReal.toReal_lt_of_lt_ofReal hAε_close
    have hApproxBound :=
      mixingErrorBound_ofSymmDiffApprox (P := Q) hA hAε hA hA
    have hApproxZero :
        |Q.real (Aε ∩ A) - Q.real Aε * Q.real A| = 0 := by
      rw [hAε_eq]
      have hCyl :
          Q.real (MeasureTheory.cylinder sA SA ∩ A) =
            Q.real (MeasureTheory.cylinder sA SA) * Q.real A := by
        simpa [Q, sA, SA] using
          shiftInvariantEvent_cylinder_real_eq_product
            (P := P) (X := X) (p := p) hirr hπ hA hshiftA (s := sA) (A0 := SA) hSA
      simp [hCyl]
    have hsymmAA :
        (A \ A) ∪ (A \ A) = (∅ : Set (Stream' E)) := by
      simp
    -- Proof comment: approximate the invariant event by a finite cylinder and use exact
    -- independence of invariant events from cylinders.
    calc
      |Q.real A - Q.real A * Q.real A|
          = |Q.real (A ∩ A) - Q.real A * Q.real A| := by simp
      _ ≤ |Q.real (Aε ∩ A) - Q.real Aε * Q.real A| +
            (2 * Q.real ((A \ Aε) ∪ (Aε \ A)) + 2 * Q.real ((A \ A) ∪ (A \ A))) := by
              simpa [add_assoc, add_left_comm, add_comm] using hApproxBound
      _ = 2 * Q.real (A ∆ Aε) := by
            rw [hApproxZero]
            simp [Set.symmDiff_def, hsymmAA]
      _ < ε := by
            dsimp [δ] at hAε_closeReal ⊢
            nlinarith
  have habs_zero : |Q.real A - Q.real A * Q.real A| = 0 := by
    by_contra hne
    have hpos : 0 < |Q.real A - Q.real A * Q.real A| := by
      exact lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    exact (not_lt_of_ge le_rfl) (hsmall _ hpos)
  have hsub : Q.real A - Q.real A * Q.real A = 0 := abs_eq_zero.mp habs_zero
  linarith

/-- Part (1) of Theorem 20.29: under the stationary mixture law
`P_π = ∑ x, π{x} P_x` of an irreducible positive recurrent Markov chain, the induced canonical
process on `E^ℕ₀` is ergodic for the one-sided shift under its stationary path law. -/
theorem stationary_shift_ergodic_of_irreducible_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    Ergodic Stream'.tail (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    infer_instance
  have hPres : MeasurePreserving Stream'.tail Q Q := by
    simpa [Q] using stationary_shift_measurePreserving (P := P) (X := X) (p := p) hπ
  refine { toMeasurePreserving := hPres, toPreErgodic := ?_ }
  refine ⟨?_⟩
  intro A hA hshiftA
  have hsq : Q.real A = Q.real A * Q.real A := by
    simpa [Q] using
      shiftInvariantEvent_real_eq_sq_of_irreducible_positiveRecurrent
        (P := P) (X := X) (p := p) hirr hπ hA hshiftA
  have hA_nonneg : 0 ≤ Q.real A := by
    exact MeasureTheory.measureReal_nonneg
  have hA_le_one : Q.real A ≤ 1 := by
    simpa using (MeasureTheory.measureReal_le_one (μ := Q) (s := A))
  have hZeroOrOne : Q.real A = 0 ∨ Q.real A = 1 := by
    have hmul : Q.real A * (1 - Q.real A) = 0 := by
      nlinarith [hsq]
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr <| by linarith
  rcases hZeroOrOne with hA0 | hA1
  · exact Filter.eventuallyConst_set'.2 <| Or.inl <| ae_eq_empty.2 <|
      (MeasureTheory.measureReal_eq_zero_iff (μ := Q) (s := A)).mp hA0
  · have hA1_measure : Q A = 1 := by
      exact (ENNReal.toReal_eq_one_iff (Q A)).mp (by simpa [Measure.real] using hA1)
    have hA_compl : Q Aᶜ = 0 := by
      rw [measure_compl hA (measure_ne_top Q A), IsProbabilityMeasure.measure_univ, hA1_measure,
        tsub_self]
    exact Filter.eventuallyConst_set'.2 <| Or.inr <| ae_eq_univ.2 hA_compl

/-- Helper for Theorem 20.29: the stationary path-law mass of a measurable event is the
`π`-average of the realized path-kernel row masses of that event. -/
lemma stationaryProcessPathLaw_real_eq_setIntegral_realizationPathKernel
    {π : ProbabilityMeasure E} {B : Set (Stream' E)} (hB : MeasurableSet B) :
    (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)).real B =
      ∫ y, (realizationPathKernel (p := p) P X y).real B ∂(π : Measure E) := by
  -- Proof comment: rewrite the stationary path law as the mixture of the path-kernel rows and
  -- then evaluate that mixture on the measurable event `B`.
  rw [stationaryProcessPathLaw_eq_comp_realizationPathKernel (P := P) (X := X) (p := p) π]
  simpa using
    (kernelCompRestrictMapRealEqSetIntegral
      (κ := realizationPathKernel (p := p) P X) (μ := (π : Measure E)) (Y := fun y : E ↦ y)
      (hY := measurable_id) (B := Set.univ) (A := B) MeasurableSet.univ hB)

/-- Helper for Theorem 20.29: shifting a future path by `n` steps is the same as moving the
starting time of the future path from `N` to `N + n`. -/
lemma futurePathPreimage_iterateTail_eq
    (N n : ℕ) (B : Set (Stream' E)) :
    (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B) =
      (shiftedPath X (N + n)) ⁻¹' B := by
  -- Proof comment: `Stream'.tail^[n]` deletes the first `n` shifted coordinates, which is the
  -- same as starting the shifted path directly at time `N + n`.
  ext ω
  change ((Stream'.tail^[n]) (shiftedPath X N ω)) ∈ B ↔
    (fun k : ℕ ↦ X ((N + n) + k) ω) ∈ B
  simpa [shiftedPath, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    congrArg (fun f : Stream' E ↦ f ∈ B)
      (funext fun k ↦ tailIterate_apply (E := E) n (shiftedPath X N ω) k)

/-- Helper for Theorem 20.29: aperiodicity forces the shifted row mass of every measurable path
event to converge to the stationary path-law mass of that event. -/
lemma realizationPathKernel_iterateTail_tendsto_stationaryProcessPathLaw_of_aperiodic
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    (haper : IsAperiodic (discreteMatrixKernel p))
    {B : Set (Stream' E)} (hB : MeasurableSet B) (x : E) :
    Tendsto
      (fun n : ℕ ↦
        (realizationPathKernel (p := p) P X x).real ((Stream'.tail^[n]) ⁻¹' B))
      atTop
      (𝓝 ((stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)).real B)) := by
  let hp : IsStochasticMatrix p := stochasticMatrix_of_markovProcessRealization (p := p) P X
  letI : IsMarkovKernel (discreteMatrixKernel p) := discreteMatrixKernel_isMarkovKernel p hp
  let f : E → ℝ := fun y : E ↦ (realizationPathKernel (p := p) P X y).real B
  have hf_meas : Measurable f := by
    -- Proof comment: the row mass of a measurable path event varies measurably with the start
    -- state.
    simpa [f] using realizationPathKernel_real_measurable (p := p) (P := P) (X := X) hB
  have hf_bound : ∀ y : E, ‖f y‖ ≤ 1 := by
    intro y
    have hnonneg : 0 ≤ f y := by
      exact MeasureTheory.measureReal_nonneg
    have hle : f y ≤ 1 := by
      simpa [f] using
        (MeasureTheory.measureReal_le_one
          (μ := realizationPathKernel (p := p) P X y) (s := B))
    rw [Real.norm_of_nonneg hnonneg]
    exact hle
  have htv :
      Tendsto
        (fun n : ℕ ↦ 2 * totalVariationDistance (nStepLaw p (diracProba x) n) π)
        atTop (𝓝 0) := by
    simpa using
      (Filter.Tendsto.const_mul (2 : ℝ)
        (nStepLaw_tendsto_invariantDistribution_of_irreducible_aperiodic
          (P := P) (X := X) (p := p) hirr hπ haper x))
  have hbound :
      ∀ n : ℕ,
        |(realizationPathKernel (p := p) P X x).real ((Stream'.tail^[n]) ⁻¹' B) -
            (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)).real B| ≤
          2 * totalVariationDistance (nStepLaw p (diracProba x) n) π := by
    intro n
    have hrow :
        ((nStepLaw p (diracProba x) n : ProbabilityMeasure E) : Measure E) =
          ((discreteMatrixKernel p ^ n) x) := by
      simpa [nStepLaw] using
        kernelComp_diracProba_eq_row (κ := discreteMatrixKernel p ^ n) x
    -- Proof comment: both target masses are averages of the same bounded observable `f`; the
    -- total-variation estimate controls the gap between the evolving state law and `π`.
    calc
      |(realizationPathKernel (p := p) P X x).real ((Stream'.tail^[n]) ⁻¹' B) -
          (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)).real B|
          =
            |∫ y, f y ∂((discreteMatrixKernel p ^ n) x) -
                ∫ y, f y ∂(π : Measure E)| := by
              rw [realizationPathKernel_iterateTail_real_eq_kernelAverage
                    (p := p) (P := P) (X := X) hB x n,
                  stationaryProcessPathLaw_real_eq_setIntegral_realizationPathKernel
                    (P := P) (X := X) (p := p) (π := π) hB]
      _ =
          |∫ y, f y ∂((nStepLaw p (diracProba x) n : ProbabilityMeasure E) : Measure E) -
              ∫ y, f y ∂(π : Measure E)| := by
            rw [hrow]
      _ ≤ 2 * totalVariationDistance (nStepLaw p (diracProba x) n) π := by
            exact integral_sub_abs_le_two_mul_totalVariationDistance
              (μ := nStepLaw p (diracProba x) n) (ν := π) hf_meas hf_bound
  have habs :
      Tendsto
        (fun n : ℕ ↦
          |(realizationPathKernel (p := p) P X x).real ((Stream'.tail^[n]) ⁻¹' B) -
              (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)).real B|)
        atTop (𝓝 0) := by
    exact squeeze_zero (fun _ ↦ abs_nonneg _) hbound htv
  -- Proof comment: convergence of the absolute gap is exactly convergence to the stationary
  -- path-law mass.
  exact (tendsto_iff_dist_tendsto_zero.2 <| by simpa [Real.dist_eq] using habs)

/-- Helper for Theorem 20.29: a shifted finite-cylinder correlation under the stationary path law
can be rewritten as a history/future event under the stationary realization law. -/
lemma stationaryCylinder_shiftedTail_eq_historyFuture
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    {s : Finset ℕ} {A0 : Set (s → E)} (hA0 : MeasurableSet A0)
    {B : Set (Stream' E)} (hB : MeasurableSet B) (n : ℕ) :
    let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
    let A : Set (Stream' E) := MeasureTheory.cylinder s A0
    let traj : Ω → Stream' E := fun ω : Ω ↦ fun k : ℕ ↦ X k ω
    let N : ℕ := s.sup id
    let AΩ : Set Ω := traj ⁻¹' A
    Q.real (A ∩ (Stream'.tail^[N + n]) ⁻¹' B) =
      (stationaryLaw P π).real
        (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)) := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  let A : Set (Stream' E) := MeasureTheory.cylinder s A0
  let traj : Ω → Stream' E := fun ω : Ω ↦ fun k : ℕ ↦ X k ω
  let N : ℕ := s.sup id
  let AΩ : Set Ω := traj ⁻¹' A
  have hA : MeasurableSet A := by
    -- Proof comment: a finite cylinder is measurable because it is the preimage of its base set
    -- under the finite restriction map.
    simpa [A, MeasureTheory.cylinder] using
      hA0.preimage (Finset.measurable_restrict s)
  have hShiftB : MeasurableSet ((Stream'.tail^[N + n]) ⁻¹' B) := by
    exact ((measurable_tail (E := E)).iterate (N + n) hB)
  -- Proof comment: unfold the stationary path law once, then identify the pulled-back tail event
  -- with the corresponding future-path event at time `N`.
  calc
    Q.real (A ∩ (Stream'.tail^[N + n]) ⁻¹' B)
        = (stationaryLaw P π).real
            (traj ⁻¹' (A ∩ (Stream'.tail^[N + n]) ⁻¹' B)) := by
              simpa [Q, traj] using
                congrArg ENNReal.toReal
                  (stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
                    (P := P) (X := X) (p := p) π (A := A ∩ (Stream'.tail^[N + n]) ⁻¹' B)
                    (hA := hA.inter hShiftB))
    _ = (stationaryLaw P π).real
          (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)) := by
            have hpre :
                traj ⁻¹' (A ∩ (Stream'.tail^[N + n]) ⁻¹' B) =
                  AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B) := by
              calc
                traj ⁻¹' (A ∩ (Stream'.tail^[N + n]) ⁻¹' B)
                    = traj ⁻¹' A ∩ traj ⁻¹' ((Stream'.tail^[N + n]) ⁻¹' B) := by
                        rw [Set.preimage_inter]
                _ = AΩ ∩ traj ⁻¹' ((Stream'.tail^[N + n]) ⁻¹' B) := by
                      rfl
                _ = AΩ ∩ (shiftedPath X (N + n)) ⁻¹' B := by
                      simpa [traj] using
                        congrArg (fun s : Set Ω ↦ AΩ ∩ s)
                          (trajectoryPreimage_iterateTail_eq_futurePathPreimage
                            (X := X) (n := N + n) (B := B))
                _ = AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B) := by
                      rw [futurePathPreimage_iterateTail_eq
                        (X := X) (N := N) (n := n) (B := B)]
            rw [hpre]

/-- Helper for Theorem 20.29: under the stationary realization law, the correlation of a history
event with a far-future path event converges to the product of the corresponding stationary
masses when the chain is aperiodic. -/
lemma historyEvent_shiftedTail_real_tendsto_product_of_aperiodic
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    (haper : IsAperiodic (discreteMatrixKernel p))
    {N : ℕ} {AΩ : Set Ω}
    (hAΩ : MeasurableSet[generatedFiltrationSpace X N] AΩ)
    {B : Set (Stream' E)} (hB : MeasurableSet B) :
    let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
    Tendsto
      (fun n : ℕ ↦
        (stationaryLaw P π).real
          (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)))
      atTop
      (𝓝 ((stationaryLaw P π).real AΩ * Q.real B)) := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  let μ : Measure Ω := stationaryLaw P π
  let f : ℕ → Ω → ℝ := fun n ω ↦
    (realizationPathKernel (p := p) P X (X N ω)).real ((Stream'.tail^[n]) ⁻¹' B)
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X :=
    inferInstance
  have hgenerated_le : generatedFiltrationSpace X N ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X N]
    exact (measurable_pastPath X hReal.measurable_process N).comap_le
  have hAΩ_ambient : MeasurableSet AΩ := hgenerated_le AΩ hAΩ
  have hf_meas :
      ∀ n : ℕ, AEStronglyMeasurable (f n) (μ.restrict AΩ) := by
    intro n
    have hmeas :
        Measurable fun ω : Ω ↦
          (realizationPathKernel (p := p) P X (X N ω)).real ((Stream'.tail^[n]) ⁻¹' B) := by
      -- Proof comment: row masses of measurable shifted events vary measurably with the current
      -- state at time `N`.
      exact
        (realizationPathKernel_real_measurable
          (p := p) (P := P) (X := X)
          ((measurable_tail (E := E)).iterate n hB)).comp (hReal.measurable_process N)
    exact hmeas.aestronglyMeasurable
  have hf_bound :
      ∀ n : ℕ, ∀ᵐ ω ∂(μ.restrict AΩ), ‖f n ω‖ ≤ 1 := by
    intro n
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    have hnonneg : 0 ≤ f n ω := MeasureTheory.measureReal_nonneg
    have hle : f n ω ≤ 1 := by
      simpa [f] using
        (MeasureTheory.measureReal_le_one
          (μ := realizationPathKernel (p := p) P X (X N ω))
          (s := (Stream'.tail^[n]) ⁻¹' B))
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hf_lim :
      ∀ᵐ ω ∂(μ.restrict AΩ), Tendsto (fun n : ℕ ↦ f n ω) atTop (𝓝 (Q.real B)) := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    -- Proof comment: aperiodicity makes the shifted row mass from the current state converge to
    -- the stationary path-law mass.
    simpa [Q, f] using
      realizationPathKernel_iterateTail_tendsto_stationaryProcessPathLaw_of_aperiodic
        (P := P) (X := X) (p := p) hirr hπ haper hB (X N ω)
  have hDCT :
      Tendsto (fun n : ℕ ↦ ∫ ω, f n ω ∂(μ.restrict AΩ)) atTop
        (𝓝 (∫ ω, Q.real B ∂(μ.restrict AΩ))) := by
    -- Proof comment: the integrands are uniformly bounded by `1`, so dominated convergence
    -- applies on the restricted stationary realization law.
    exact MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : Ω ↦ (1 : ℝ))
      hf_meas
      (integrable_const (1 : ℝ))
      hf_bound
      hf_lim
  have hRewrite :
      ∀ n : ℕ,
        (stationaryLaw P π).real
            (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)) =
          ∫ ω, f n ω ∂(μ.restrict AΩ) := by
    intro n
    -- Proof comment: rewrite the history/future event by the stationary-law path-kernel integral
    -- formula, then view the set integral as an integral over the restricted measure.
    calc
      (stationaryLaw P π).real
          (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B))
          = ∫ ω in AΩ, f n ω ∂μ := by
              simpa [μ, f] using
                stationaryLaw_historyEvent_futurePath_apply_eq_setIntegral_pathKernel
                  (P := P) (X := X) (p := p) (π := π) (N := N)
                  (AΩ := AΩ) hAΩ ((measurable_tail (E := E)).iterate n hB)
      _ = ∫ ω, f n ω ∂(μ.restrict AΩ) := by
            rfl
  have hLimitConst :
      ∫ ω, Q.real B ∂(μ.restrict AΩ) = (stationaryLaw P π).real AΩ * Q.real B := by
    rw [← MeasureTheory.integral_indicator hAΩ_ambient]
    simpa [μ, smul_eq_mul] using
      (MeasureTheory.integral_indicator_const
        (μ := stationaryLaw P π) (Q.real B) hAΩ_ambient)
  have hMain :
      Tendsto
        (fun n : ℕ ↦
          (stationaryLaw P π).real
            (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)))
        atTop
        (𝓝 ((stationaryLaw P π).real AΩ * Q.real B)) := by
    have hDCT' :
        Tendsto (fun n : ℕ ↦ ∫ ω, f n ω ∂(μ.restrict AΩ)) atTop
          (𝓝 ((stationaryLaw P π).real AΩ * Q.real B)) := by
      simpa [hLimitConst] using hDCT
    exact Tendsto.congr'
      (Filter.Eventually.of_forall fun n ↦ (hRewrite n).symm)
      hDCT'
  simpa [Q] using hMain

/-- Helper for Theorem 20.29: if the first event is a finite cylinder, then its shifted
correlation with any measurable target event converges to the product of the stationary masses
when the chain is aperiodic. -/
lemma finiteCylinder_shiftCorrelation_tendsto_product_of_aperiodic
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) (π : Measure E))
    (haper : IsAperiodic (discreteMatrixKernel p))
    {s : Finset ℕ} {A0 : Set (s → E)} (hA0 : MeasurableSet A0)
    {B : Set (Stream' E)} (hB : MeasurableSet B) :
    let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
    let A : Set (Stream' E) := MeasureTheory.cylinder s A0
    Tendsto (fun n : ℕ ↦ Q.real (A ∩ (Stream'.tail^[n]) ⁻¹' B)) atTop
      (𝓝 (Q.real A * Q.real B)) := by
  let Q : Measure (Stream' E) := stationaryProcessPathLaw (p := p) P X π
  let A : Set (Stream' E) := MeasureTheory.cylinder s A0
  let traj : Ω → Stream' E := fun ω : Ω ↦ fun k : ℕ ↦ X k ω
  let N : ℕ := s.sup id
  let AΩ : Set Ω := traj ⁻¹' A
  have hAΩ :
      MeasurableSet[generatedFiltrationSpace X N] AΩ := by
    simpa [AΩ, A, traj, N] using
      cylinderTrajectoryPreimage_measurableInFiltration (X := X) (s := s) (A0 := A0) hA0
  have hA :
      MeasurableSet A := by
    simpa [A, MeasureTheory.cylinder] using hA0.preimage (Finset.measurable_restrict s)
  have hQA :
      Q.real A = (stationaryLaw P π).real AΩ := by
    simpa [Q, A, AΩ, traj] using
      congrArg ENNReal.toReal
        (stationaryProcessPathLaw_apply_eq_stationaryLaw_preimage
          (P := P) (X := X) (p := p) π (A := A) hA)
  have hShifted :
      Tendsto (fun n : ℕ ↦ Q.real (A ∩ (Stream'.tail^[N + n]) ⁻¹' B)) atTop
        (𝓝 (Q.real A * Q.real B)) := by
    have hHist :
        Tendsto
          (fun n : ℕ ↦
            (stationaryLaw P π).real
              (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)))
          atTop
          (𝓝 ((stationaryLaw P π).real AΩ * Q.real B)) := by
      simpa [Q] using
        historyEvent_shiftedTail_real_tendsto_product_of_aperiodic
          (P := P) (X := X) (p := p) hirr hπ haper (N := N) (AΩ := AΩ) hAΩ (B := B) hB
    have hRewrite :
        ∀ n : ℕ,
          Q.real (A ∩ (Stream'.tail^[N + n]) ⁻¹' B) =
            (stationaryLaw P π).real
              (AΩ ∩ (shiftedPath X N) ⁻¹' ((Stream'.tail^[n]) ⁻¹' B)) := by
      intro n
      simpa [Q, A, traj, N, AΩ] using
        stationaryCylinder_shiftedTail_eq_historyFuture
          (P := P) (X := X) (p := p) (π := π) hπ (s := s) (A0 := A0) hA0 (B := B) hB n
    have hMain :
        Tendsto (fun n : ℕ ↦ Q.real (A ∩ (Stream'.tail^[N + n]) ⁻¹' B)) atTop
          (𝓝 ((stationaryLaw P π).real AΩ * Q.real B)) := by
      exact Tendsto.congr' (Filter.Eventually.of_forall fun n ↦ (hRewrite n).symm) hHist
    simpa [hQA] using hMain
  -- Route correction: prove the `N`-shifted sequence converges first, then remove the finite
  -- prefix by an explicit tail argument on `ℕ`.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rcases Metric.tendsto_atTop.1 hShifted ε hε with ⟨M, hM⟩
  refine ⟨N + M, ?_⟩
  intro n hn
  have hNn : N ≤ n := le_trans (Nat.le_add_right N M) hn
  let m : ℕ := n - N
  have hn_eq : n = N + m := by
    dsimp [m]
    exact (Nat.add_sub_of_le hNn).symm
  have hMm : M ≤ m := by
    have haux : N + M ≤ n := hn
    have haux' : N + M ≤ N + m := by
      simpa [hn_eq] using haux
    exact Nat.add_le_add_iff_left.mp haux'
  have htail : |Q.real (A ∩ (Stream'.tail^[N + m]) ⁻¹' B) - Q.real A * Q.real B| < ε :=
    hM m hMm
  simpa [hn_eq] using htail
/-- Theorem 20.29 (2): under the stationary mixture law of an irreducible positive recurrent
Markov chain, the induced canonical process on `E^ℕ₀` is strongly mixing for the one-sided shift
exactly when the transition kernel is aperiodic. -/
theorem stationary_shift_mixing_iff_aperiodic_of_irreducible_positiveRecurrent
    (hirr : IsIrreducibleMarkovChain P X)
    {π : ProbabilityMeasure E}
    (hπ : Kernel.Invariant (discreteMatrixKernel p) π.toMeasure) :
    IsStronglyMixing Stream'.tail
      (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E)) ↔
      IsAperiodic (discreteMatrixKernel p) := by
  constructor
  · intro hmix
    classical
    by_contra haper
    let Q : Measure (Stream' E) := (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
    obtain ⟨x, hxPeriod⟩ : ∃ x : E, statePeriod (discreteMatrixKernel p) x ≠ 1 := by
      simpa [IsAperiodic, HasPeriod] using haper
    let Ax : Set (Stream' E) := {ω | ω 0 = x}
    have hAx_meas : MeasurableSet Ax := by
      -- Proof comment: the obstruction event depends only on the zeroth coordinate.
      change MeasurableSet ((Function.eval 0 : Stream' E → E) ⁻¹' ({x} : Set E))
      exact (measurable_pi_apply 0 : Measurable (Function.eval 0 : Stream' E → E))
        (measurableSet_singleton x)
    have hπx_pos : 0 < π {x} :=
      invariantDistribution_apply_singleton_pos (P := P) (X := X) hirr hπ x
    have hAx_mass : Q Ax = π {x} := by
      -- Proof comment: the correlation lemma with `n = 0` identifies the singleton event mass.
      have hzeroCorr :
          Q Ax = π {x} * ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) := by
        simpa [Q, Ax] using
          zeroCoordinateSingletonCorrelation_eq_invariantMass_mul_stepMass
          (P := P) (X := X) (p := p) (π := π) x 0
      have hpowZero :
          ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) = 1 := by
        change (Kernel.id x) ({x} : Set E) = 1
        simp [Kernel.id_apply]
      calc
        Q Ax = π {x} * ((discreteMatrixKernel p ^ 0) x) ({x} : Set E) := hzeroCorr
        _ = π {x} * 1 := by rw [hpowZero]
        _ = π {x} := by simp
    have hAx_real_pos : 0 < Q.real Ax := by
      rw [MeasureTheory.measureReal_def, hAx_mass]
      exact ENNReal.toReal_pos
        (by simpa using hπx_pos.ne')
        (by simpa using measure_ne_top (μ := (π : Measure E)) ({x} : Set E))
    have hzero_far :
        ∀ N : ℕ, ∃ n ≥ N, Q (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax) = 0 := by
      intro N
      by_cases hperiod_zero : statePeriod (discreteMatrixKernel p) x = 0
      · let m : ℕ := N + 1
        refine ⟨m, Nat.le_succ _, ?_⟩
        have hndvd : ¬ statePeriod (discreteMatrixKernel p) x ∣ (N + 1) := by
          simp [hperiod_zero]
        have hreturn_zero :
            ((discreteMatrixKernel p ^ m) x) ({x} : Set E) = 0 := by
          by_contra hreturn_ne_zero
          have hmem : m ∈ positiveTransitionStepSet (discreteMatrixKernel p) x x := by
            simpa [mem_positiveTransitionStepSet_iff] using
              (bot_lt_iff_ne_bot.mpr hreturn_ne_zero)
          exact hndvd (statePeriod_dvd_of_mem_positiveTransitionStepSet
            (discreteMatrixKernel p) x hmem)
        simpa [Q, Ax, m, hreturn_zero] using
          zeroCoordinateSingletonCorrelation_eq_invariantMass_mul_stepMass
            (P := P) (X := X) (p := p) (π := π) x m
      · let n : ℕ := N * statePeriod (discreteMatrixKernel p) x + 1
        refine ⟨n, ?_, ?_⟩
        · have hperiod_pos : 0 < statePeriod (discreteMatrixKernel p) x :=
            Nat.pos_of_ne_zero hperiod_zero
          exact le_trans (Nat.le_mul_of_pos_right N hperiod_pos) (Nat.le_succ _)
        have hndvd : ¬ statePeriod (discreteMatrixKernel p) x ∣ n := by
          -- Proof comment: a divisor of `N * period + 1` would also divide `1`, forcing period
          -- `1`, contrary to the chosen periodic obstruction state.
          intro hdvd
          have hmod_zero : n % statePeriod (discreteMatrixKernel p) x = 0 :=
            Nat.mod_eq_zero_of_dvd hdvd
          have hlt : 1 < statePeriod (discreteMatrixKernel p) x := by
            omega
          have hmod_one : n % statePeriod (discreteMatrixKernel p) x = 1 := by
            simp [n, Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hlt]
          omega
        have hreturn_zero :
            ((discreteMatrixKernel p ^ n) x) ({x} : Set E) = 0 := by
          by_contra hreturn_ne_zero
          have hmem : n ∈ positiveTransitionStepSet (discreteMatrixKernel p) x x := by
            simpa [mem_positiveTransitionStepSet_iff] using
              (bot_lt_iff_ne_bot.mpr hreturn_ne_zero)
          exact hndvd (statePeriod_dvd_of_mem_positiveTransitionStepSet
            (discreteMatrixKernel p) x hmem)
        simpa [Q, Ax, n, hreturn_zero] using
          zeroCoordinateSingletonCorrelation_eq_invariantMass_mul_stepMass
            (P := P) (X := X) (p := p) (π := π) x n
    have hlimit := hmix Ax Ax hAx_meas hAx_meas
    have hhalf_pos : 0 < Q.real Ax * Q.real Ax / 2 := by
      positivity
    rcases Metric.tendsto_atTop.1 hlimit (Q.real Ax * Q.real Ax / 2) hhalf_pos with ⟨N, hN⟩
    rcases hzero_far N with ⟨n, hnN, hzero⟩
    have hclose := hN n hnN
    have htarget_nonneg : 0 ≤ Q.real Ax * Q.real Ax := by positivity
    have hcontra : Q.real Ax * Q.real Ax < Q.real Ax * Q.real Ax / 2 := by
      have hzero_real :
          Q.real (Ax ∩ (Stream'.tail^[n]) ⁻¹' Ax) = 0 := by
        rw [MeasureTheory.measureReal_def, hzero]
        simp
      rw [hzero_real] at hclose
      have hclose' : |0 - (Q.real Ax * Q.real Ax)| < Q.real Ax * Q.real Ax / 2 := by
        simpa [Real.dist_eq] using hclose
      simpa [sub_eq_add_neg, abs_neg, abs_of_nonneg htarget_nonneg] using hclose'
    linarith
  · intro haper
    let Q : Measure (Stream' E) := (stationaryProcessPathLaw (p := p) P X π : Measure (Stream' E))
    letI : IsProbabilityMeasure Q := by
      dsimp [Q]
      infer_instance
    have hPres : MeasurePreserving Stream'.tail Q Q := by
      -- Proof comment: the stationary path law is already known to be shift-invariant.
      simpa [Q] using stationary_shift_measurePreserving (P := P) (X := X) (p := p) hπ
    intro A B hA hB
    have hdense : Q.MeasureDense (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) := by
      -- Proof comment: finite-coordinate cylinders form a measure-dense set algebra on the path
      -- space, exactly as in the Bernoulli-shift approximation shell.
      refine Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
          (μ := Q)
          (𝒜 := MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E))
          MeasureTheory.isSetAlgebra_measurableCylinders ?_
      simpa using
        (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℕ ↦ E)).symm
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    let δ : ℝ := ε / 4
    have hδ : 0 < δ := by
      positivity
    rcases hdense.fin_meas_approx hA (measure_ne_top Q A) δ hδ with
      ⟨Aε, hAε_mem, -, hAε_close⟩
    let sA : Finset ℕ := MeasureTheory.measurableCylinders.finset hAε_mem
    let SA : Set ((i : sA) → E) := MeasureTheory.measurableCylinders.set hAε_mem
    have hAε_eq : Aε = MeasureTheory.cylinder sA SA :=
      MeasureTheory.measurableCylinders.eq_cylinder hAε_mem
    have hAε : MeasurableSet Aε := MeasurableSet.of_mem_measurableCylinders hAε_mem
    have hSA : MeasurableSet SA := MeasureTheory.measurableCylinders.measurableSet hAε_mem
    have hAε_limit :
        Tendsto (fun n : ℕ ↦ Q.real (Aε ∩ (Stream'.tail^[n]) ⁻¹' B)) atTop
          (𝓝 (Q.real Aε * Q.real B)) := by
      rw [hAε_eq]
      simpa [Q, sA, SA] using
        finiteCylinder_shiftCorrelation_tendsto_product_of_aperiodic
          (P := P) (X := X) (p := p) hirr hπ haper (s := sA) (A0 := SA) hSA (B := B) hB
    have hAε_closeReal : Q.real (A ∆ Aε) < δ := by
      simpa [Measure.real_def, δ] using ENNReal.toReal_lt_of_lt_ofReal hAε_close
    have hhalf_pos : 0 < ε / 2 := by positivity
    rcases Metric.tendsto_atTop.1 hAε_limit (ε / 2) hhalf_pos with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hPreB : MeasurableSet ((Stream'.tail^[n]) ⁻¹' B) := by
      exact hB.preimage (hPres.iterate n).measurable
    have hPreBReal : Q.real ((Stream'.tail^[n]) ⁻¹' B) = Q.real B := by
      simpa [Measure.real_def] using
        congrArg ENNReal.toReal
          ((hPres.iterate n).measure_preimage (s := B) hB.nullMeasurableSet)
    have hApproxBound :=
      mixingErrorBound_ofSymmDiffApprox (P := Q) hA hAε hPreB hPreB
    have hApproxClose :
        |Q.real (Aε ∩ (Stream'.tail^[n]) ⁻¹' B) - Q.real Aε * Q.real B| < ε / 2 := by
      simpa [Real.dist_eq] using hN n hn
    have hsymmA :
        (A \ Aε) ∪ (Aε \ A) = A ∆ Aε := by
      ext x
      simp [Set.mem_symmDiff]
    -- Proof comment: approximate only the left event by a cylinder, keep the right event fixed,
    -- and absorb the single symmetric-difference error into the final `ε`-estimate.
    calc
      |Q.real (A ∩ (Stream'.tail^[n]) ⁻¹' B) - Q.real A * Q.real B|
          = |Q.real (A ∩ (Stream'.tail^[n]) ⁻¹' B) -
              Q.real A * Q.real ((Stream'.tail^[n]) ⁻¹' B)| := by
                rw [hPreBReal]
      _ ≤ |Q.real (Aε ∩ (Stream'.tail^[n]) ⁻¹' B) -
            Q.real Aε * Q.real ((Stream'.tail^[n]) ⁻¹' B)| +
            (2 * Q.real ((A \ Aε) ∪ (Aε \ A)) +
              2 * Q.real ((((Stream'.tail^[n]) ⁻¹' B) \ ((Stream'.tail^[n]) ⁻¹' B)) ∪
                (((Stream'.tail^[n]) ⁻¹' B) \ ((Stream'.tail^[n]) ⁻¹' B)))) := by
              simpa [add_assoc, add_left_comm, add_comm] using hApproxBound
      _ = |Q.real (Aε ∩ (Stream'.tail^[n]) ⁻¹' B) - Q.real Aε * Q.real B| +
            2 * Q.real (A ∆ Aε) := by
              rw [hPreBReal]
              simp [hsymmA]
      _ < ε := by
            dsimp [δ] at hAε_closeReal ⊢
            nlinarith

end

end ProbabilityTheory

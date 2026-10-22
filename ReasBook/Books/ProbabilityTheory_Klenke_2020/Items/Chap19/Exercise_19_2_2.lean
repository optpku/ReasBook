/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_15
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

attribute [local instance] Classical.propDecidable

namespace ProbabilityTheory

/-- The occupancy states of the `K`-urn model with `N` indistinguishable balls, represented as
weak compositions of `N` indexed by the urns. -/
abbrev GibbsUrnState (K N : ℕ) :=
  {η : Fin K → ℕ // η ∈ Finset.piAntidiag Finset.univ N}

/-- The Boltzmann weight `exp (-β W_j)` of the target urn `j`. -/
def gibbsUrnTargetWeight {K : ℕ} (β : ℝ) (W : Fin K → ℝ) (j : Fin K) : ℝ :=
  Real.exp (-β * W j)

/-- The normalizing constant `Z = ∑_j exp (-β W_j)` for the Gibbs relocation law. -/
def gibbsUrnPartitionFunction {K : ℕ} (β : ℝ) (W : Fin K → ℝ) : ℝ :=
  ∑ j : Fin K, gibbsUrnTargetWeight β W j

/-- The Gibbs relocation law on the urn labels. -/
def gibbsUrnTargetDistribution {K : ℕ} (β : ℝ) (W : Fin K → ℝ) : Fin K → ℝ≥0∞ :=
  fun j ↦ ENNReal.ofReal (gibbsUrnTargetWeight β W j / gibbsUrnPartitionFunction β W)

/-- The predicate that `η'` is obtained from `η` by choosing a ball from urn `i` and moving it to
urn `j`. -/
def IsGibbsUrnSingleBallMove {K N : ℕ} (η η' : GibbsUrnState K N) (i j : Fin K) : Prop :=
  0 < η.1 i ∧
    if i = j then
      η' = η
    else
      η'.1 i + 1 = η.1 i ∧ η'.1 j = η.1 j + 1 ∧ ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k

/-- The one-step transition matrix of the occupancy chain: first choose a ball uniformly, then
resample its destination urn according to the Gibbs law. -/
def gibbsUrnTransitionMatrix (K N : ℕ) (β : ℝ) (W : Fin K → ℝ) :
    GibbsUrnState K N → GibbsUrnState K N → ℝ≥0∞ :=
  fun η η' ↦
    ∑ i : Fin K,
      (((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
        ∑ j : Fin K,
          if IsGibbsUrnSingleBallMove η η' i j then gibbsUrnTargetDistribution β W j else 0

/-- The multinomial Gibbs weight of an occupancy state. -/
def gibbsUrnOccupancyWeight (K N : ℕ) (β : ℝ) (W : Fin K → ℝ) (η : GibbsUrnState K N) :
    ℝ≥0∞ :=
  (Nat.multinomial Finset.univ η.1 : ℝ≥0∞) *
    ∏ j : Fin K, gibbsUrnTargetDistribution β W j ^ η.1 j

-- Proof sketch: the numerator is the finite Boltzmann sum `∑_j exp (-β W_j)`, and `hK` ensures
-- this sum is strictly positive because at least one index contributes a positive exponential term;
-- dividing each Boltzmann factor by this common normalizing constant makes the total mass `1`.
/-- The Gibbs relocation probabilities sum to one over the `K` urns. -/
theorem gibbsUrnTargetDistribution_sum {K : ℕ} (β : ℝ) (W : Fin K → ℝ) (hK : 0 < K) :
    ∑ j : Fin K, gibbsUrnTargetDistribution β W j = 1 := by
  obtain ⟨j₀⟩ := Fin.pos_iff_nonempty.mp hK
  have hZ_pos : 0 < gibbsUrnPartitionFunction β W := by
    -- Proof comment: at least one positive exponential term appears in the finite partition sum.
    unfold gibbsUrnPartitionFunction
    have hj₀_le :
        gibbsUrnTargetWeight β W j₀ ≤ ∑ j : Fin K, gibbsUrnTargetWeight β W j := by
      exact Finset.single_le_sum
        (fun j _ ↦ le_of_lt (by simpa [gibbsUrnTargetWeight] using Real.exp_pos (-(β * W j))))
        (Finset.mem_univ j₀)
    exact lt_of_lt_of_le
      (by simpa [gibbsUrnTargetWeight] using Real.exp_pos (-(β * W j₀))) hj₀_le
  have hZ_nonneg : 0 ≤ gibbsUrnPartitionFunction β W := le_of_lt hZ_pos
  -- Proof comment: after collecting the common denominator, the normalized Boltzmann weights sum
  -- to `Z / Z`.
  simp_rw [gibbsUrnTargetDistribution]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · have hsum_div :
        (∑ i : Fin K, gibbsUrnTargetWeight β W i / gibbsUrnPartitionFunction β W) = 1 := by
      rw [← Finset.sum_div]
      have hsum_ne_zero : (∑ i : Fin K, gibbsUrnTargetWeight β W i) ≠ 0 := by
        exact ne_of_gt (by simpa [gibbsUrnPartitionFunction] using hZ_pos)
      rw [gibbsUrnPartitionFunction, div_self hsum_ne_zero]
    rw [hsum_div]
    norm_num
  · intro j _
    exact div_nonneg
      (le_of_lt (by simpa [gibbsUrnTargetWeight] using Real.exp_pos (-(β * W j)))) hZ_nonneg

-- Proof sketch: apply the multinomial theorem to the probability vector
-- `gibbsUrnTargetDistribution β W`; after using `gibbsUrnTargetDistribution_sum`, the total mass
-- becomes `(∑_j q_j)^N = 1^N = 1`.
/-- The multinomial Gibbs weights form a probability vector on the occupancy states. -/
theorem gibbsUrnOccupancyWeight_sum {K N : ℕ} (β : ℝ) (W : Fin K → ℝ) (hK : 0 < K) :
    ∑ η : GibbsUrnState K N, gibbsUrnOccupancyWeight K N β W η = 1 := by
  -- Proof comment: rewrite the subtype sum as the canonical multinomial expansion over
  -- `Finset.piAntidiag univ N`, then collapse it using that the Gibbs target law has total mass
  -- `1`.
  calc
    ∑ η : GibbsUrnState K N, gibbsUrnOccupancyWeight K N β W η
      = (∑ j : Fin K, gibbsUrnTargetDistribution β W j) ^ N := by
          symm
          calc
            (∑ j : Fin K, gibbsUrnTargetDistribution β W j) ^ N
              = ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin K)) N,
                  (Nat.multinomial Finset.univ k : ℝ≥0∞) *
                    ∏ j : Fin K, gibbsUrnTargetDistribution β W j ^ k j := by
                      simpa using
                        (Finset.sum_pow_eq_sum_piAntidiag
                          (s := (Finset.univ : Finset (Fin K)))
                          (f := gibbsUrnTargetDistribution β W) N)
            _ = ∑ η : GibbsUrnState K N, gibbsUrnOccupancyWeight K N β W η := by
                  rw [← Finset.sum_attach]
                  simp [GibbsUrnState, gibbsUrnOccupancyWeight]
    _ = 1 := by
          rw [gibbsUrnTargetDistribution_sum β W hK]
          simp

/-- The multinomial Gibbs distribution on occupancy states. -/
def gibbsUrnInvariantDistribution (K N : ℕ) (β : ℝ) (W : Fin K → ℝ) (hK : 0 < K) :
    ProbabilityMeasure (GibbsUrnState K N) :=
  ⟨(PMF.ofFintype (gibbsUrnOccupancyWeight K N β W) (gibbsUrnOccupancyWeight_sum β W hK)).toMeasure,
    inferInstance⟩

/-- Helper for Exercise 19.2.2: the Gibbs invariant distribution assigns each singleton occupancy
state its multinomial Gibbs weight. -/
theorem gibbsUrnInvariantDistribution_apply_singleton {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hK : 0 < K) (η : GibbsUrnState K N) :
    (gibbsUrnInvariantDistribution K N β W hK : Measure (GibbsUrnState K N)) {η} =
      gibbsUrnOccupancyWeight K N β W η := by
  -- Proof comment: unfold the PMF-built probability measure and evaluate it on the singleton.
  simp [gibbsUrnInvariantDistribution, PMF.ofFintype_apply]

/-- Helper for Exercise 19.2.2: the off-diagonal occupancy profile obtained by moving one ball
from urn `i` to urn `j`. -/
private def gibbsUrnOffDiagMovedCounts {K N : ℕ} (η : GibbsUrnState K N) (i j : Fin K) :
    Fin K → ℕ :=
  Function.update (Function.update η.1 i (η.1 i - 1)) j (η.1 j + 1)

/-- Helper for Exercise 19.2.2: after the off-diagonal move, the source urn count is decreased by
one. -/
private theorem gibbsUrnOffDiagMovedCounts_apply_source {K N : ℕ} (η : GibbsUrnState K N)
    {i j : Fin K} (hij : i ≠ j) :
    gibbsUrnOffDiagMovedCounts η i j i = η.1 i - 1 := by
  -- Proof comment: the second update does not touch the source coordinate because `i ≠ j`.
  simp [gibbsUrnOffDiagMovedCounts, hij]

/-- Helper for Exercise 19.2.2: after the off-diagonal move, the target urn count is increased by
one. -/
private theorem gibbsUrnOffDiagMovedCounts_apply_target {K N : ℕ} (η : GibbsUrnState K N)
    {i j : Fin K} :
    gibbsUrnOffDiagMovedCounts η i j j = η.1 j + 1 := by
  -- Proof comment: the outer update sets the target coordinate directly.
  simp [gibbsUrnOffDiagMovedCounts]

/-- Helper for Exercise 19.2.2: every other urn count is unchanged by an off-diagonal move. -/
private theorem gibbsUrnOffDiagMovedCounts_apply_other {K N : ℕ} (η : GibbsUrnState K N)
    {i j k : Fin K} (hki : k ≠ i) (hkj : k ≠ j) :
    gibbsUrnOffDiagMovedCounts η i j k = η.1 k := by
  -- Proof comment: both updates miss coordinates different from `i` and `j`.
  simp [gibbsUrnOffDiagMovedCounts, hki, hkj]

/-- Helper for Exercise 19.2.2: the off-diagonal moved occupancy profile still has total mass
`N`. -/
private theorem gibbsUrnOffDiagMovedCounts_mem_piAntidiag {K N : ℕ} (η : GibbsUrnState K N)
    {i j : Fin K} (hij : i ≠ j) (hi : 0 < η.1 i) :
    gibbsUrnOffDiagMovedCounts η i j ∈ Finset.piAntidiag Finset.univ N := by
  refine (Finset.mem_piAntidiag).2 ?_
  constructor
  · have hηsum : ∑ k : Fin K, η.1 k = N := (Finset.mem_piAntidiag.mp η.2).1
    -- Proof comment: split the finite sum at the two moved coordinates; the `-1` and `+1`
    -- contributions cancel, while every untouched coordinate stays fixed.
    calc
      ∑ k : Fin K, gibbsUrnOffDiagMovedCounts η i j k
        = gibbsUrnOffDiagMovedCounts η i j i +
            Finset.sum ((Finset.univ : Finset (Fin K)).erase i) (gibbsUrnOffDiagMovedCounts η i j) := by
              symm
              exact Finset.add_sum_erase (s := (Finset.univ : Finset (Fin K)))
                (f := gibbsUrnOffDiagMovedCounts η i j) (h := Finset.mem_univ i)
      _ = (η.1 i - 1) +
            (gibbsUrnOffDiagMovedCounts η i j j +
              Finset.sum (((Finset.univ : Finset (Fin K)).erase i).erase j)
                (gibbsUrnOffDiagMovedCounts η i j)) := by
              rw [gibbsUrnOffDiagMovedCounts_apply_source η hij]
              congr 1
              symm
              exact Finset.add_sum_erase (s := ((Finset.univ : Finset (Fin K)).erase i))
                (f := gibbsUrnOffDiagMovedCounts η i j)
                (h := Finset.mem_erase.mpr ⟨fun hji ↦ hij hji.symm, by simp⟩)
      _ = (η.1 i - 1) +
            ((η.1 j + 1) +
              Finset.sum (((Finset.univ : Finset (Fin K)).erase i).erase j) η.1) := by
              rw [gibbsUrnOffDiagMovedCounts_apply_target η]
              congr 2
              refine Finset.sum_congr rfl ?_
              intro k hk
              have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
              have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
              rw [gibbsUrnOffDiagMovedCounts_apply_other η hki hkj]
      _ = η.1 i +
            (η.1 j + Finset.sum (((Finset.univ : Finset (Fin K)).erase i).erase j) η.1) := by
              omega
      _ = η.1 i + Finset.sum ((Finset.univ : Finset (Fin K)).erase i) η.1 := by
            congr 1
            exact Finset.add_sum_erase (s := ((Finset.univ : Finset (Fin K)).erase i))
              (f := η.1)
              (h := Finset.mem_erase.mpr ⟨fun hji ↦ hij hji.symm, by simp⟩)
      _ = ∑ k : Fin K, η.1 k := by
            exact Finset.add_sum_erase (s := (Finset.univ : Finset (Fin K)))
              (f := η.1) (h := Finset.mem_univ i)
      _ = N := hηsum
  · intro k _
    exact Finset.mem_univ k

/-- Helper for Exercise 19.2.2: the bundled occupancy state obtained by moving one ball from urn
`i` to urn `j`. -/
private def gibbsUrnOffDiagMovedState {K N : ℕ} (η : GibbsUrnState K N) (i j : Fin K)
    (hij : i ≠ j) (hi : 0 < η.1 i) : GibbsUrnState K N :=
  ⟨gibbsUrnOffDiagMovedCounts η i j, gibbsUrnOffDiagMovedCounts_mem_piAntidiag η hij hi⟩

/-- Helper for Exercise 19.2.2: any source urn with at least one ball admits the claimed single
ball move to any target urn. -/
private theorem gibbsUrnSingleBallMove_exists {K N : ℕ} {η : GibbsUrnState K N} {i j : Fin K}
    (hi : 0 < η.1 i) :
    ∃ η' : GibbsUrnState K N, IsGibbsUrnSingleBallMove η η' i j := by
  by_cases hij : i = j
  · subst hij
    -- Proof comment: on the diagonal, choosing and replacing a ball in the same urn leaves the
    -- occupancy profile unchanged.
    exact ⟨η, by simp [IsGibbsUrnSingleBallMove, hi]⟩
  · refine ⟨gibbsUrnOffDiagMovedState η i j hij hi, ?_⟩
    have hsource :
        (gibbsUrnOffDiagMovedState η i j hij hi).1 i + 1 = η.1 i := by
      -- Proof comment: subtracting one from a positive occupancy count and then adding one
      -- recovers the original count.
      change gibbsUrnOffDiagMovedCounts η i j i + 1 = η.1 i
      rw [gibbsUrnOffDiagMovedCounts_apply_source η hij]
      omega
    refine ⟨hi, ?_⟩
    -- Proof comment: the bundled moved state has exactly the expected source, target, and
    -- untouched coordinates.
    simpa [IsGibbsUrnSingleBallMove, hij, gibbsUrnOffDiagMovedState] using
      (And.intro hsource
        (And.intro
          (gibbsUrnOffDiagMovedCounts_apply_target η)
          (fun k hki hkj ↦ gibbsUrnOffDiagMovedCounts_apply_other η hki hkj)))

/-- Helper for Exercise 19.2.2: for fixed `i` and `j`, the resulting moved occupancy state is
unique. -/
private theorem gibbsUrnSingleBallMove_unique {K N : ℕ} {η η₁ η₂ : GibbsUrnState K N}
    {i j : Fin K} (h₁ : IsGibbsUrnSingleBallMove η η₁ i j)
    (h₂ : IsGibbsUrnSingleBallMove η η₂ i j) :
    η₁ = η₂ := by
  by_cases hij : i = j
  · rcases h₁ with ⟨-, h₁'⟩
    rcases h₂ with ⟨-, h₂'⟩
    have hη₁ : η₁ = η := by simpa [hij] using h₁'
    have hη₂ : η₂ = η := by simpa [hij] using h₂'
    exact hη₁.trans hη₂.symm
  · rcases h₁ with ⟨-, h₁'⟩
    rcases h₂ with ⟨-, h₂'⟩
    rcases (by simpa [hij] using h₁' :
      η₁.1 i + 1 = η.1 i ∧ η₁.1 j = η.1 j + 1 ∧
        ∀ k : Fin K, k ≠ i → k ≠ j → η₁.1 k = η.1 k) with
      ⟨hi₁, hj₁, hrest₁⟩
    rcases (by simpa [hij] using h₂' :
      η₂.1 i + 1 = η.1 i ∧ η₂.1 j = η.1 j + 1 ∧
        ∀ k : Fin K, k ≠ i → k ≠ j → η₂.1 k = η.1 k) with
      ⟨hi₂, hj₂, hrest₂⟩
    apply Subtype.ext
    ext k
    by_cases hki : k = i
    · subst hki
      omega
    by_cases hkj : k = j
    · subst hkj
      exact hj₁.trans hj₂.symm
    · exact (hrest₁ k hki hkj).trans (hrest₂ k hki hkj).symm

/-- Helper for Exercise 19.2.2: summing a constant contribution over all moved occupancy states
for fixed `i` and `j` leaves exactly one copy when urn `i` is nonempty. -/
private theorem gibbsUrnSum_singleBallMove {K N : ℕ} {η : GibbsUrnState K N} {i j : Fin K}
    (a : ℝ≥0∞) :
    ∑ η' : GibbsUrnState K N, (if IsGibbsUrnSingleBallMove η η' i j then a else 0) =
      if 0 < η.1 i then a else 0 := by
  classical
  by_cases hi : 0 < η.1 i
  · obtain ⟨η₀, hη₀⟩ := gibbsUrnSingleBallMove_exists (i := i) (j := j) hi
    rw [if_pos hi]
    calc
      ∑ η' : GibbsUrnState K N, (if IsGibbsUrnSingleBallMove η η' i j then a else 0)
          = if IsGibbsUrnSingleBallMove η η₀ i j then a else 0 := by
            refine Finset.sum_eq_single η₀ ?_ ?_
            · intro η' _ hη'
              by_cases hmove : IsGibbsUrnSingleBallMove η η' i j
              · exfalso
                exact hη' (gibbsUrnSingleBallMove_unique hmove hη₀)
              · simp [hmove]
            · intro hη₀_mem
              exact False.elim (hη₀_mem (Finset.mem_univ η₀))
      _ = a := by simp [hη₀]
  · rw [if_neg hi]
    refine Finset.sum_eq_zero ?_
    intro η' _
    by_cases hmove : IsGibbsUrnSingleBallMove η η' i j
    · rcases hmove with ⟨hi', -⟩
      exact False.elim (hi hi')
    · simp [hmove]

/-- Helper for Exercise 19.2.2: reversing a single-ball move swaps the source and target urns. -/
private theorem gibbsUrnSingleBallMove_reverse {K N : ℕ} {η η' : GibbsUrnState K N}
    {i j : Fin K} (hij : i ≠ j) (hmove : IsGibbsUrnSingleBallMove η η' i j) :
    IsGibbsUrnSingleBallMove η' η j i := by
  rcases hmove with ⟨hi, hmove⟩
  have hmove' : η'.1 i + 1 = η.1 i ∧ η'.1 j = η.1 j + 1 ∧
      ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k := by
    simpa [hij] using hmove
  rcases hmove' with ⟨hiCoord, hjCoord, hrest⟩
  refine ⟨by
    -- Proof comment: the target urn contains one more ball after the move, so it is nonempty in
    -- the reverse move.
    rw [hjCoord]
    exact Nat.succ_pos _, ?_⟩
  -- Proof comment: the reverse move swaps the decrement and increment coordinates.
  simp [IsGibbsUrnSingleBallMove, hij, hij.symm, hiCoord, hjCoord]
  intro k hkj hki
  exact (hrest k hki hkj).symm

/-- Helper for Exercise 19.2.2: the single-ball move relation is symmetric after swapping the
source and target urns. -/
private theorem gibbsUrnSingleBallMove_iff_reverse {K N : ℕ} {η η' : GibbsUrnState K N}
    {i j : Fin K} :
    IsGibbsUrnSingleBallMove η η' i j ↔ IsGibbsUrnSingleBallMove η' η j i := by
  by_cases hij : i = j
  · subst hij
    constructor
    · rintro ⟨hi, hdiag⟩
      -- Proof comment: a diagonal move forces `η' = η`, so reversing it changes nothing.
      have hη' : η' = η := by simpa using hdiag
      subst η'
      simpa [IsGibbsUrnSingleBallMove, hi]
    · rintro ⟨hi, hdiag⟩
      -- Proof comment: the same diagonal normalization works in the reverse direction.
      have hη : η = η' := by simpa using hdiag
      subst η'
      simpa [IsGibbsUrnSingleBallMove, hi]
  · constructor
    · exact gibbsUrnSingleBallMove_reverse hij
    · exact gibbsUrnSingleBallMove_reverse (fun hji ↦ hij hji.symm)

/-- Helper for Exercise 19.2.2: on a countable discrete state space, singleton detailed balance
implies setwise reversibility of `discreteMatrixKernel p`. -/
private theorem discreteMatrixKernel_flow
    {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {p : S → S → ℝ≥0∞} {π : Measure S}
    (A B : Set S) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    ∫⁻ x in A, discreteMatrixKernel p x B ∂π =
      ∑' x : S, if x ∈ A then ∑' y : S, if y ∈ B then p x y * π ({x} : Set S) else 0 else 0 := by
  classical
  -- Proof comment: rewrite the restricted integral as an indicator integral and expand it over
  -- the countable discrete state space.
  rw [← lintegral_indicator hA, MeasureTheory.lintegral_countable']
  refine tsum_congr fun x ↦ ?_
  by_cases hx : x ∈ A
  · rw [if_pos hx, Set.indicator_of_mem hx]
    rw [discreteMatrixKernel_apply, Measure.sum_apply _ hB]
    have hdirac :
        (fun y : S ↦ (p x y • Measure.dirac y) B) = fun y : S ↦ if y ∈ B then p x y else 0 := by
      funext y
      by_cases hy : y ∈ B <;> simp [Measure.smul_apply, hy]
    rw [hdirac]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (ENNReal.tsum_mul_right (a := π ({x} : Set S)) (f := fun y : S ↦ if y ∈ B then p x y else 0)).symm
  · rw [if_neg hx, Set.indicator_of_notMem hx, zero_mul]

/-- Helper for Exercise 19.2.2: splitting a finite product over `Fin K` into two distinguished
coordinates and the untouched remainder. -/
private theorem gibbsUrnProdSplitTwoCoords {K : ℕ} {α : Type*} [CommMonoid α]
    (g : Fin K → α) {i j : Fin K} (hij : i ≠ j) :
    (∏ k : Fin K, g k) =
      g i * (g j *
        Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j) g) := by
  -- Proof comment: peel off the source factor `i`, then peel off the target factor `j` from the
  -- remaining product over `univ.erase i`.
  calc
    (∏ k : Fin K, g k) = g i * (((Finset.univ : Finset (Fin K)).erase i).prod g) := by
      symm
      exact Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin K))) (f := g)
        (h := Finset.mem_univ i)
    _ = g i * (g j * ((((Finset.univ : Finset (Fin K)).erase i).erase j).prod g)) := by
      rw [← Finset.mul_prod_erase
        (s := ((Finset.univ : Finset (Fin K)).erase i)) (f := g)
        (h := Finset.mem_erase.mpr ⟨fun hji ↦ hij hji.symm, by simp⟩)]

/-- Helper for Exercise 19.2.2: the factorial contribution of the untouched urns is unchanged by a
single off-diagonal move. -/
private theorem gibbsUrnFactorialProdSplitTwoCoords {K : ℕ} (f : Fin K → ℕ) {i j : Fin K}
    (hij : i ≠ j) :
    (∏ k : Fin K, Nat.factorial (f k)) =
      Nat.factorial (f i) *
        (Nat.factorial (f j) *
          Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
            (fun k ↦ Nat.factorial (f k))) := by
  -- Proof comment: this specializes the generic two-coordinate product split to the factorial
  -- normal form used by the multinomial identity.
  simpa using gibbsUrnProdSplitTwoCoords (g := fun k ↦ Nat.factorial (f k)) hij

/-- Helper for Exercise 19.2.2: the factorial contribution of the untouched urns is unchanged by a
single off-diagonal move. -/
private theorem gibbsUrnMoveFactorialRest {K N : ℕ} {η η' : GibbsUrnState K N} {i j : Fin K}
    (hrest : ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k) :
    Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
        (fun k ↦ Nat.factorial (η'.1 k)) =
      Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
        (fun k ↦ Nat.factorial (η.1 k)) := by
  -- Proof comment: factorials of all urns away from the source and target coordinates are
  -- unchanged by the move.
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  rw [hrest k hki hkj]

/-- Helper for Exercise 19.2.2: the factorial contribution of the untouched urns is unchanged by a
single off-diagonal move. -/
private theorem gibbsUrnMoveMultinomialBalanceNat {K N : ℕ} {η η' : GibbsUrnState K N}
    {i j : Fin K} (hmove : IsGibbsUrnSingleBallMove η η' i j) :
    Nat.multinomial Finset.univ η.1 * η.1 i =
      Nat.multinomial Finset.univ η'.1 * η'.1 j := by
  by_cases hij : i = j
  · rcases hmove with ⟨hi, hdiag⟩
    have hη' : η' = η := by simpa [IsGibbsUrnSingleBallMove, hi, hij] using hdiag
    subst hη'
    subst hij
    rfl
  · rcases hmove with ⟨hi, hmove'⟩
    have hmove'' :
        η'.1 i + 1 = η.1 i ∧ η'.1 j = η.1 j + 1 ∧
          ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k := by
      simpa [IsGibbsUrnSingleBallMove, hij] using hmove'
    rcases hmove'' with ⟨hiCoord, hjCoord, hrest⟩
    set rest : ℕ :=
      Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
        (fun k ↦ Nat.factorial (η.1 k))
    have hrestFactorial :
        Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
            (fun k ↦ Nat.factorial (η'.1 k)) =
          rest := by
      -- Proof comment: the off-diagonal move leaves all untouched factorial factors unchanged.
      simpa [rest] using gibbsUrnMoveFactorialRest (η := η) (η' := η') (i := i) (j := j) hrest
    have hprodη :
        ∏ k : Fin K, Nat.factorial (η.1 k) =
          Nat.factorial (η.1 i) * (Nat.factorial (η.1 j) * rest) := by
      -- Proof comment: isolate the two moved coordinates from the factorial product of `η`.
      simpa [rest] using gibbsUrnFactorialProdSplitTwoCoords (f := η.1) hij
    have hprodη' :
        ∏ k : Fin K, Nat.factorial (η'.1 k) =
          Nat.factorial (η'.1 i) * (Nat.factorial (η'.1 j) * rest) := by
      -- Proof comment: the same split for `η'` uses the unchanged untouched factorial product.
      calc
        ∏ k : Fin K, Nat.factorial (η'.1 k)
          = Nat.factorial (η'.1 i) *
              (Nat.factorial (η'.1 j) *
                Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
                  (fun k ↦ Nat.factorial (η'.1 k))) := by
              simpa using gibbsUrnFactorialProdSplitTwoCoords (f := η'.1) hij
        _ = Nat.factorial (η'.1 i) * (Nat.factorial (η'.1 j) * rest) := by
              rw [hrestFactorial]
    have hsumη : ∑ k : Fin K, η.1 k = N := (Finset.mem_piAntidiag.mp η.2).1
    have hsumη' : ∑ k : Fin K, η'.1 k = N := (Finset.mem_piAntidiag.mp η'.2).1
    have hspec :
        (Nat.factorial (η.1 i) * (Nat.factorial (η.1 j) * rest)) *
            Nat.multinomial Finset.univ η.1 =
          (Nat.factorial (η'.1 i) * (Nat.factorial (η'.1 j) * rest)) *
            Nat.multinomial Finset.univ η'.1 := by
      -- Proof comment: both split factorial products realize the same total factorial `N!`.
      calc
        (Nat.factorial (η.1 i) * (Nat.factorial (η.1 j) * rest)) *
            Nat.multinomial Finset.univ η.1
          = Nat.factorial (∑ k ∈ (Finset.univ : Finset (Fin K)), η.1 k) := by
              simpa [hprodη] using (Nat.multinomial_spec (Finset.univ : Finset (Fin K)) η.1)
        _ = Nat.factorial N := by simpa using congrArg Nat.factorial hsumη
        _ = Nat.factorial (∑ k ∈ (Finset.univ : Finset (Fin K)), η'.1 k) := by
              simpa using (congrArg Nat.factorial hsumη').symm
        _ = (Nat.factorial (η'.1 i) * (Nat.factorial (η'.1 j) * rest)) *
              Nat.multinomial Finset.univ η'.1 := by
              simpa [hprodη'] using
                (Nat.multinomial_spec (Finset.univ : Finset (Fin K)) η'.1).symm
    have hcommon :
        (Nat.factorial (η'.1 i) * (Nat.factorial (η.1 j) * rest)) *
            (Nat.multinomial Finset.univ η.1 * η.1 i) =
          (Nat.factorial (η'.1 i) * (Nat.factorial (η.1 j) * rest)) *
            (Nat.multinomial Finset.univ η'.1 * η'.1 j) := by
      -- Proof comment: rewrite the moved factorials with `Nat.factorial_succ` so both sides share
      -- the same untouched common factor.
      calc
        (Nat.factorial (η'.1 i) * (Nat.factorial (η.1 j) * rest)) *
            (Nat.multinomial Finset.univ η.1 * η.1 i)
          = (Nat.factorial (η.1 i) * (Nat.factorial (η.1 j) * rest)) *
              Nat.multinomial Finset.univ η.1 := by
              rw [← hiCoord, Nat.factorial_succ]
              simp [mul_assoc, mul_left_comm, mul_comm]
        _ = (Nat.factorial (η'.1 i) * (Nat.factorial (η'.1 j) * rest)) *
              Nat.multinomial Finset.univ η'.1 := hspec
        _ = (Nat.factorial (η'.1 i) * (Nat.factorial (η.1 j) * rest)) *
              (Nat.multinomial Finset.univ η'.1 * η'.1 j) := by
              rw [hjCoord, Nat.factorial_succ]
              simp [mul_assoc, mul_left_comm, mul_comm]
    have hcommon_pos :
        0 < (Nat.factorial (η'.1 i) * (Nat.factorial (η.1 j) * rest)) := by
      -- Proof comment: every factorial factor is positive, hence so is their finite product.
      refine Nat.mul_pos (Nat.factorial_pos _) ?_
      refine Nat.mul_pos (Nat.factorial_pos _) ?_
      dsimp [rest]
      exact Finset.prod_pos fun _ _ ↦ Nat.factorial_pos _
    exact Nat.eq_of_mul_eq_mul_left hcommon_pos hcommon

/-- Helper for Exercise 19.2.2: isolating the two moved coordinates in the Gibbs target product. -/
private theorem gibbsUrnTargetProductSplitTwoCoords {K : ℕ} (q : Fin K → ℝ≥0∞) (f : Fin K → ℕ)
    {i j : Fin K} (hij : i ≠ j) :
    (∏ k : Fin K, q k ^ f k) =
      q i ^ f i *
        (q j ^ f j *
          Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j) (fun k ↦ q k ^ f k)) := by
  -- Proof comment: this is exactly the generic two-coordinate product split specialized to the
  -- Gibbs factors `q k ^ f k`.
  simpa using gibbsUrnProdSplitTwoCoords (g := fun k ↦ q k ^ f k) hij

/-- Helper for Exercise 19.2.2: the untouched Gibbs target factors agree before and after a single
off-diagonal move. -/
private theorem gibbsUrnMoveTargetProductRest {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    {η η' : GibbsUrnState K N} {i j : Fin K}
    (hrest : ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k) :
    Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
        (fun k ↦ gibbsUrnTargetDistribution β W k ^ η'.1 k) =
      Finset.prod (((Finset.univ : Finset (Fin K)).erase i).erase j)
        (fun k ↦ gibbsUrnTargetDistribution β W k ^ η.1 k) := by
  -- Proof comment: every factor in the remainder product lies away from the moved coordinates, so
  -- `hrest` identifies the source and target exponents pointwise.
  refine Finset.prod_congr rfl ?_
  intro k hk
  have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
  have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  rw [hrest k hki hkj]

/-- Helper for Exercise 19.2.2: on a countable discrete state space, singleton detailed balance
implies setwise reversibility of `discreteMatrixKernel p`. -/
private theorem discreteMatrixKernelIsReversibleOfDetailedBalance
    {S : Type*} [Countable S] [MeasurableSpace S] [DiscreteMeasurableSpace S]
    {p : S → S → ℝ≥0∞} {π : Measure S}
    (hbal : ∀ x y : S, p x y * π ({x} : Set S) = p y x * π ({y} : Set S)) :
    Kernel.IsReversible (discreteMatrixKernel p) π := by
  classical
  intro A B hA hB
  let flowTerm : S → S → ℝ≥0∞ := fun x y ↦
    if x ∈ A ∧ y ∈ B then p x y * π ({x} : Set S) else 0
  have hflow_left :
      (∑' x : S, if x ∈ A then (∑' y : S, if y ∈ B then p x y * π ({x} : Set S) else 0) else 0) =
        ∑' x : S, ∑' y : S, flowTerm x y := by
    -- Proof comment: fold the separate `A` and `B` membership tests into one two-variable flow
    -- term on `A × B`.
    refine tsum_congr fun x ↦ ?_
    by_cases hx : x ∈ A <;> simp [flowTerm, hx]
  have hflow_right :
      (∑' y : S, if y ∈ B then (∑' x : S, if x ∈ A then p y x * π ({y} : Set S) else 0) else 0) =
        ∑' y : S, ∑' x : S, flowTerm x y := by
    -- Proof comment: detailed balance converts the reversed edge weight back to the forward flow
    -- term before swapping the countable sums.
    refine tsum_congr fun y ↦ ?_
    by_cases hy : y ∈ B
    · rw [if_pos hy]
      refine tsum_congr fun x ↦ ?_
      by_cases hx : x ∈ A <;> simp [flowTerm, hx, hy, hbal y x]
    · simp [flowTerm, hy]
  calc
    ∫⁻ x in A, discreteMatrixKernel p x B ∂π
      = ∑' x : S, if x ∈ A then (∑' y : S, if y ∈ B then p x y * π ({x} : Set S) else 0) else 0 :=
          discreteMatrixKernel_flow (p := p) (π := π) A B hA hB
    _ = ∑' x : S, ∑' y : S, flowTerm x y := hflow_left
    _ = ∑' y : S, ∑' x : S, flowTerm x y := ENNReal.tsum_comm
    _ = ∑' y : S, if y ∈ B then (∑' x : S, if x ∈ A then p y x * π ({y} : Set S) else 0) else 0 :=
          hflow_right.symm
    _ = ∫⁻ x in B, discreteMatrixKernel p x A ∂π :=
          (discreteMatrixKernel_flow (p := p) (π := π) B A hB hA).symm

/-- Helper for Exercise 19.2.2: a single-ball move preserves the multinomial coefficient after the
chosen-source factor is transferred to the destination count. -/
private theorem gibbsUrnMoveMultinomialBalance {K N : ℕ} {η η' : GibbsUrnState K N}
    {i j : Fin K} (hmove : IsGibbsUrnSingleBallMove η η' i j) :
    (Nat.multinomial Finset.univ η.1 : ℝ≥0∞) * η.1 i =
      (Nat.multinomial Finset.univ η'.1 : ℝ≥0∞) * η'.1 j := by
  -- Proof comment: first prove the factorial identity in `ℕ`, then cast it to `ℝ≥0∞`.
  exact_mod_cast gibbsUrnMoveMultinomialBalanceNat hmove

/-- Helper for Exercise 19.2.2: a single-ball move shifts exactly one Gibbs target factor from the
source urn to the destination urn. -/
private theorem gibbsUrnMoveTargetProductBalance {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    {η η' : GibbsUrnState K N} {i j : Fin K} (hmove : IsGibbsUrnSingleBallMove η η' i j) :
    (∏ k : Fin K, gibbsUrnTargetDistribution β W k ^ η.1 k) * gibbsUrnTargetDistribution β W j =
      (∏ k : Fin K, gibbsUrnTargetDistribution β W k ^ η'.1 k) *
        gibbsUrnTargetDistribution β W i := by
  by_cases hij : i = j
  · rcases hmove with ⟨hi, hdiag⟩
    have hη' : η' = η := by simpa [IsGibbsUrnSingleBallMove, hi, hij] using hdiag
    subst hη'
    subst hij
    rfl
  · rcases hmove with ⟨hi, hmove'⟩
    have hmove'' :
        η'.1 i + 1 = η.1 i ∧ η'.1 j = η.1 j + 1 ∧
          ∀ k : Fin K, k ≠ i → k ≠ j → η'.1 k = η.1 k := by
      simpa [IsGibbsUrnSingleBallMove, hij] using hmove'
    rcases hmove'' with ⟨hiCoord, hjCoord, hrest⟩
    have hrestProd :=
      gibbsUrnMoveTargetProductRest (β := β) (W := W) (η := η) (η' := η')
        (i := i) (j := j) hrest
    -- Proof comment: rewrite both target products into the moved coordinates and the shared rest
    -- product, then use `pow_succ` on the shifted source and target exponents.
    rw [gibbsUrnTargetProductSplitTwoCoords (q := gibbsUrnTargetDistribution β W) (f := η.1) hij]
    rw [gibbsUrnTargetProductSplitTwoCoords (q := gibbsUrnTargetDistribution β W) (f := η'.1) hij]
    rw [hrestProd, ← hiCoord, hjCoord]
    simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 19.2.2: the full occupancy weight satisfies detailed balance along a
single-ball move. -/
private theorem gibbsUrnOccupancyWeightMoveBalance {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    {η η' : GibbsUrnState K N} {i j : Fin K} (hmove : IsGibbsUrnSingleBallMove η η' i j) :
    gibbsUrnOccupancyWeight K N β W η * η.1 i * gibbsUrnTargetDistribution β W j =
      gibbsUrnOccupancyWeight K N β W η' * η'.1 j * gibbsUrnTargetDistribution β W i := by
  -- Proof comment: unfold the occupancy weight into its multinomial and Gibbs-factor pieces, then
  -- transport each piece across the single-ball move with the two balance lemmas.
  calc
    gibbsUrnOccupancyWeight K N β W η * η.1 i * gibbsUrnTargetDistribution β W j
      = ((Nat.multinomial Finset.univ η.1 : ℝ≥0∞) * η.1 i) *
          ((∏ k : Fin K, gibbsUrnTargetDistribution β W k ^ η.1 k) *
            gibbsUrnTargetDistribution β W j) := by
              simp [gibbsUrnOccupancyWeight, mul_assoc, mul_left_comm, mul_comm]
    _ = ((Nat.multinomial Finset.univ η'.1 : ℝ≥0∞) * η'.1 j) *
          ((∏ k : Fin K, gibbsUrnTargetDistribution β W k ^ η'.1 k) *
            gibbsUrnTargetDistribution β W i) := by
              rw [gibbsUrnMoveMultinomialBalance hmove, gibbsUrnMoveTargetProductBalance β W hmove]
    _ = gibbsUrnOccupancyWeight K N β W η' * η'.1 j * gibbsUrnTargetDistribution β W i := by
          simp [gibbsUrnOccupancyWeight, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Exercise 19.2.2: the `π(η)`-weighted `(i,j)` transition term matches the reversed
`π(η')`-weighted `(j,i)` term. -/
private theorem gibbsUrnTransitionTermBalance {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    {η η' : GibbsUrnState K N} {i j : Fin K} :
    gibbsUrnOccupancyWeight K N β W η *
        ((((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
          (if IsGibbsUrnSingleBallMove η η' i j then gibbsUrnTargetDistribution β W j else 0)) =
      gibbsUrnOccupancyWeight K N β W η' *
        ((((η'.1 j : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
          (if IsGibbsUrnSingleBallMove η' η j i then gibbsUrnTargetDistribution β W i else 0)) := by
  by_cases hmove : IsGibbsUrnSingleBallMove η η' i j
  · have hmoveRev : IsGibbsUrnSingleBallMove η' η j i :=
      (gibbsUrnSingleBallMove_iff_reverse).mp hmove
    -- Proof comment: when the move is present, both indicator terms are active and the remaining
    -- equality is exactly the occupancy-weight balance multiplied by the common factor `N⁻¹`.
    calc
      gibbsUrnOccupancyWeight K N β W η *
          ((((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
            (if IsGibbsUrnSingleBallMove η η' i j then gibbsUrnTargetDistribution β W j else 0))
        = (gibbsUrnOccupancyWeight K N β W η * η.1 i * gibbsUrnTargetDistribution β W j) *
            (N : ℝ≥0∞)⁻¹ := by
              simp [hmove, hmoveRev, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      _ = (gibbsUrnOccupancyWeight K N β W η' * η'.1 j * gibbsUrnTargetDistribution β W i) *
            (N : ℝ≥0∞)⁻¹ := by
              rw [gibbsUrnOccupancyWeightMoveBalance β W hmove]
      _ = gibbsUrnOccupancyWeight K N β W η' *
            ((((η'.1 j : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
              (if IsGibbsUrnSingleBallMove η' η j i then
                gibbsUrnTargetDistribution β W i else 0)) := by
              simp [hmove, hmoveRev, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  · have hmoveRev : ¬ IsGibbsUrnSingleBallMove η' η j i := by
      simpa [gibbsUrnSingleBallMove_iff_reverse] using hmove
    -- Proof comment: when no move connects `η` to `η'`, both indicators vanish after reversing
    -- the move relation.
    simp [hmove, hmoveRev]

-- Proof sketch: if `N = 0`, then every row index lies in the empty state space unless `K > 0`,
-- so the row-sum condition is vacuous. For `N > 0`, fix an occupancy `η` and sum the transition
-- probabilities over all possible one-ball moves: the choice probabilities `η i / N` sum to `1`
-- because `η` contains exactly `N` balls, and the relocation probabilities sum to `1` by
-- `gibbsUrnTargetDistribution_sum`.
/-- The Gibbs urn transition matrix is stochastic, so it defines a discrete-time Markov chain on
the occupancy states. -/
theorem gibbsUrnTransitionMatrix_isStochastic {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hN : 0 < N) :
    IsStochasticMatrix (gibbsUrnTransitionMatrix K N β W) := by
  intro η
  by_cases hK : 0 < K
  · have hηsum : ∑ i : Fin K, η.1 i = N := (Finset.mem_piAntidiag.mp η.2).1
    rw [tsum_fintype]
    calc
      ∑ η' : GibbsUrnState K N, gibbsUrnTransitionMatrix K N β W η η'
          = ∑ i : Fin K,
              (((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
                ∑ j : Fin K, (if 0 < η.1 i then gibbsUrnTargetDistribution β W j else 0) := by
              -- Proof comment: swap the finite sums and use the uniqueness of the moved occupancy
              -- state for fixed `i` and `j`.
              simp_rw [gibbsUrnTransitionMatrix]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl ?_
              intro i _
              rw [← Finset.mul_sum]
              rw [Finset.sum_comm]
              simp_rw [gibbsUrnSum_singleBallMove]
      _ = ∑ i : Fin K, (((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            by_cases hi : 0 < η.1 i
            · simp [hi, gibbsUrnTargetDistribution_sum β W hK]
            · have hzero : η.1 i = 0 := Nat.eq_zero_of_not_pos hi
              simp [hzero]
      _ = ((∑ i : Fin K, η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞) := by
            simp_rw [div_eq_mul_inv]
            rw [Nat.cast_sum]
            rw [← Finset.sum_mul]
      _ = (N : ℝ≥0∞) / (N : ℝ≥0∞) := by rw [hηsum]
      _ = 1 := by
            have hN0 : (N : ℝ≥0∞) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt hN)
            exact ENNReal.div_self hN0 ENNReal.coe_ne_top
  · exfalso
    have hηsum : (∑ i : Fin K, η.1 i) = N := (Finset.mem_piAntidiag.mp η.2).1
    have hK0 : K = 0 := Nat.eq_zero_of_not_pos hK
    have : 0 = N := by
      cases hK0
      simpa using hηsum
    exact (Nat.ne_of_gt hN) this.symm

-- Proof sketch: compare the detailed-balance weights of two occupancies connected by a single-ball
-- move. The multinomial coefficient changes by the usual ratio `η i / (η' j)`, which cancels the
-- factor coming from choosing a ball in urn `i`, while the Gibbs factor contributes exactly the
-- destination probability `exp (-β W_j) / Z`.
/-- Exercise 19.2.2: for the occupancy chain of `N` indistinguishable balls in `K` urns with
relocation probabilities proportional to `exp (-β W_j)`, the multinomial Gibbs distribution is a
reversing measure. In particular, it is the invariant distribution of this Markov chain. -/
theorem gibbsUrnKernel_isReversible {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hK : 0 < K) (hN : 0 < N) :
    Kernel.IsReversible (discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W))
      (gibbsUrnInvariantDistribution K N β W hK : Measure (GibbsUrnState K N)) := by
  -- Route correction: the remaining blocker is the detailed-balance normal form, not the bridge
  -- from singleton balance to kernel reversibility.
  -- Proof comment: prove singleton detailed balance by expanding the transition matrix into its
  -- double finite sum and applying the termwise balance lemma before swapping the two indices.
  refine discreteMatrixKernelIsReversibleOfDetailedBalance ?_
  intro η η'
  rw [gibbsUrnInvariantDistribution_apply_singleton β W hK η,
    gibbsUrnInvariantDistribution_apply_singleton β W hK η']
  calc
    gibbsUrnTransitionMatrix K N β W η η' * gibbsUrnOccupancyWeight K N β W η
      = ∑ i : Fin K, ∑ j : Fin K,
          gibbsUrnOccupancyWeight K N β W η *
            ((((η.1 i : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
              (if IsGibbsUrnSingleBallMove η η' i j then gibbsUrnTargetDistribution β W j else 0)) := by
              simp [gibbsUrnTransitionMatrix, Finset.sum_mul, Finset.mul_sum, mul_assoc,
                mul_left_comm, mul_comm]
    _ = ∑ i : Fin K, ∑ j : Fin K,
          gibbsUrnOccupancyWeight K N β W η' *
            ((((η'.1 j : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
              (if IsGibbsUrnSingleBallMove η' η j i then gibbsUrnTargetDistribution β W i else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              exact gibbsUrnTransitionTermBalance β W (η := η) (η' := η') (i := i) (j := j)
    _ = ∑ j : Fin K, ∑ i : Fin K,
          gibbsUrnOccupancyWeight K N β W η' *
            ((((η'.1 j : ℕ) : ℝ≥0∞) / (N : ℝ≥0∞)) *
              (if IsGibbsUrnSingleBallMove η' η j i then gibbsUrnTargetDistribution β W i else 0)) := by
              rw [Finset.sum_comm]
    _ = gibbsUrnTransitionMatrix K N β W η' η * gibbsUrnOccupancyWeight K N β W η' := by
          simp [gibbsUrnTransitionMatrix, Finset.sum_mul, Finset.mul_sum, mul_assoc,
            mul_left_comm, mul_comm]

-- Proof sketch: by `gibbsUrnTransitionMatrix_isStochastic`, the discrete kernel
-- `discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W)` is Markov; then
-- `Kernel.IsReversible.invariant` applied to
-- `gibbsUrnKernel_isReversible` yields invariance of the Gibbs law.
/-- The multinomial Gibbs law is invariant for the Gibbs urn kernel. -/
theorem gibbsUrnInvariantDistribution_isInvariant {K N : ℕ} (β : ℝ) (W : Fin K → ℝ)
    (hK : 0 < K) (hN : 0 < N) :
    Kernel.Invariant (discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W))
      (gibbsUrnInvariantDistribution K N β W hK : Measure (GibbsUrnState K N)) := by
  -- Proof comment: reversibility gives invariance once the discrete matrix kernel is known to be
  -- Markov.
  let _ : IsMarkovKernel (discreteMatrixKernel (gibbsUrnTransitionMatrix K N β W)) :=
    discreteMatrixKernel_isMarkovKernel _ (gibbsUrnTransitionMatrix_isStochastic β W hN)
  exact (gibbsUrnKernel_isReversible β W hK hN).invariant

end ProbabilityTheory

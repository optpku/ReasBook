/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.TotalVariation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- The state space `{0,1}^N`, represented as Boolean-valued functions on `Fin N`. -/
abbrev HypercubeState (N : ℕ) : Type :=
  Fin N → Bool

/-- The vertex obtained from `x` by flipping the coordinate `i`. -/
def hypercubeFlipAt {N : ℕ} (x : HypercubeState N) (i : Fin N) : HypercubeState N :=
  Function.update x i (!(x i))

/-- For Exercise 18.4.6 (1): for `N > 0`, the transition matrix of the lazy random walk on
`{0,1}^N` places mass `ε` at the current vertex and mass `(1 - ε) / N` at each vertex obtained by
flipping exactly one coordinate. -/
def hypercubeLazyTransitionMatrix (N : ℕ) [NeZero N] (ε : Set.Ioo (0 : ℝ) 1) :
    HypercubeState N → HypercubeState N → ℝ≥0∞ :=
  fun x y ↦
    if y = x then
      ENNReal.ofReal (ε : ℝ)
    else
      ∑ i : Fin N,
        if y = hypercubeFlipAt x i then
          ENNReal.ofReal ((1 - (ε : ℝ)) / N)
        else
          0

/-- The uniform distribution on the finite hypercube `{0,1}^N`. -/
def hypercubeUniformDistribution (N : ℕ) : ProbabilityMeasure (HypercubeState N) :=
  ⟨(PMF.uniformOfFintype (HypercubeState N)).toMeasure, inferInstance⟩

section LazyHypercube

variable (N : ℕ) [NeZero N] (ε : Set.Ioo (0 : ℝ) 1)

/-- The canonical Markov-kernel view of the lazy hypercube transition matrix. -/
abbrev hypercubeLazyKernel : Kernel (HypercubeState N) (HypercubeState N) :=
  discreteMatrixKernel (hypercubeLazyTransitionMatrix N ε)

/-- The modulus of the largest nontrivial eigenvalue of the lazy hypercube walk. -/
def hypercubeLazyConvergenceFactor : ℝ :=
  max (|1 - 2 * (1 - (ε : ℝ)) / N|) (|2 * (ε : ℝ) - 1|)

/-- Helper for Exercise 18.4.6: flipping the same hypercube coordinate twice returns to the
original vertex. -/
private theorem hypercubeFlipAt_involutive (x : HypercubeState N) (i : Fin N) :
    hypercubeFlipAt (hypercubeFlipAt x i) i = x := by
  -- Proof comment: evaluate both sides coordinatewise; the updated coordinate is toggled twice,
  -- while every other coordinate is unchanged by both updates.
  ext j
  by_cases hji : j = i
  · subst hji
    simp [hypercubeFlipAt]
  · simp [hypercubeFlipAt, hji]

/-- Helper for Exercise 18.4.6: flipping a hypercube coordinate changes the state. -/
private theorem hypercubeFlipAt_ne_self (x : HypercubeState N) (i : Fin N) :
    hypercubeFlipAt x i ≠ x := by
  -- Proof comment: compare the two states at the flipped coordinate `i`; equality would force a
  -- Boolean to equal its negation.
  intro h
  have hcoord : !(x i) = x i := by
    simpa [hypercubeFlipAt] using congrFun h i
  cases hxi : x i <;> simp [hxi] at hcoord

/-- Helper for Exercise 18.4.6: a coordinate flip is determined by its index. -/
private theorem hypercubeFlipAt_right_injective (x : HypercubeState N) :
    Function.Injective (fun i : Fin N ↦ hypercubeFlipAt x i) := by
  intro i j hij
  by_cases h : i = j
  · exact h
  · have hij_ne : i ≠ j := h
    have hcoord : hypercubeFlipAt x i i = hypercubeFlipAt x j i := by
      simpa using congrFun hij i
    have htoggle : !(x i) = x i := by
      simpa [hypercubeFlipAt, Function.update_of_ne hij_ne] using hcoord
    cases hxi : x i <;> simp [hxi] at htoggle

/-- Helper for Exercise 18.4.6: the discrete kernel evaluates on singletons by reading off the
transition matrix entry. -/
private theorem hypercubeLazyKernel_apply_singleton (x y : HypercubeState N) :
    hypercubeLazyKernel N ε x ({y} : Set (HypercubeState N)) =
      hypercubeLazyTransitionMatrix N ε x y := by
  -- Proof comment: expand the discrete matrix kernel as a sum of weighted Dirac masses and keep
  -- the unique singleton contribution.
  rw [hypercubeLazyKernel, discreteMatrixKernel_apply]
  simpa using
    (Measure.sum_smul_dirac_singleton
      (f := fun z : HypercubeState N ↦ hypercubeLazyTransitionMatrix N ε x z) (a := y))

/-- Helper for Exercise 18.4.6: flipping coordinate `i` is symmetric between source and target. -/
private theorem hypercubeFlipAt_eq_iff (x y : HypercubeState N) (i : Fin N) :
    y = hypercubeFlipAt x i ↔ x = hypercubeFlipAt y i := by
  constructor
  · intro h
    rw [h]
    exact (hypercubeFlipAt_involutive (N := N) x i).symm
  · intro h
    rw [h]
    exact (hypercubeFlipAt_involutive (N := N) y i).symm

/-- Helper for Exercise 18.4.6: the lazy hypercube matrix is symmetric. -/
private theorem hypercubeLazyTransitionMatrix_symm (x y : HypercubeState N) :
    hypercubeLazyTransitionMatrix N ε x y = hypercubeLazyTransitionMatrix N ε y x := by
  by_cases hxy : y = x
  · subst hxy
    rfl
  · have hyx : x ≠ y := by simpa [eq_comm] using hxy
    -- Proof comment: off the diagonal, both entries are sums over the same flip indices, and
    -- `y = hypercubeFlipAt x i` is equivalent to `x = hypercubeFlipAt y i`.
    rw [hypercubeLazyTransitionMatrix, hypercubeLazyTransitionMatrix, if_neg hxy, if_neg hyx]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hyi : y = hypercubeFlipAt x i
    · have hxi : x = hypercubeFlipAt y i := (hypercubeFlipAt_eq_iff (N := N) x y i).mp hyi
      rw [if_pos hyi, if_pos hxi]
    · have hxi : ¬ x = hypercubeFlipAt y i := by
        intro hxi
        exact hyi ((hypercubeFlipAt_eq_iff (N := N) x y i).mpr hxi)
      rw [if_neg hyi, if_neg hxi]

/-- Helper for Exercise 18.4.6: the ordered list of all hypercube coordinates. -/
private def hypercubeAllCoords : List (Fin N) :=
  List.finRange N

/-- Helper for Exercise 18.4.6: every coordinate belongs to `hypercubeAllCoords`. -/
private theorem hypercubeAllCoords_mem (i : Fin N) :
    i ∈ hypercubeAllCoords (N := N) := by
  simp [hypercubeAllCoords]

/-- Helper for Exercise 18.4.6: the list of all coordinates has no repetitions. -/
private theorem hypercubeAllCoords_nodup :
    (hypercubeAllCoords (N := N)).Nodup := by
  simpa [hypercubeAllCoords] using List.nodup_finRange N

/-- Helper for Exercise 18.4.6: flip a prescribed list of coordinates from left to right. -/
private def hypercubeFlipList (x : HypercubeState N) : List (Fin N) → HypercubeState N
  | [] => x
  | i :: is => hypercubeFlipList (hypercubeFlipAt x i) is

/-- Helper for Exercise 18.4.6: along a nodup coordinate list, `hypercubeFlipList` toggles
exactly the listed coordinates. -/
private theorem hypercubeFlipList_apply_of_nodup {l : List (Fin N)}
    (hl : l.Nodup) (x : HypercubeState N) (j : Fin N) :
    hypercubeFlipList (N := N) x l j = if j ∈ l then !(x j) else x j := by
  induction l generalizing x j with
  | nil =>
      simp [hypercubeFlipList]
  | cons i is ih =>
      simp at hl
      by_cases hji : j = i
      · subst hji
        simpa [hypercubeFlipList, hypercubeFlipAt, hl.1] using
          ih hl.2 (hypercubeFlipAt x j) j
      · have hij : i ≠ j := fun hij' ↦ hji hij'.symm
        by_cases hj : j ∈ is
        · simpa [hypercubeFlipList, List.mem_cons, hji, hj, hypercubeFlipAt,
            Function.update_of_ne hij] using
            ih hl.2 (hypercubeFlipAt x i) j
        · simpa [hypercubeFlipList, List.mem_cons, hji, hj, hypercubeFlipAt,
            Function.update_of_ne hij] using
            ih hl.2 (hypercubeFlipAt x i) j

/-- Helper for Exercise 18.4.6: the coordinates where two hypercube states differ. -/
private def hypercubeDifferingCoords (x y : HypercubeState N) : List (Fin N) :=
  (hypercubeAllCoords (N := N)).filter fun i ↦ x i ≠ y i

/-- Helper for Exercise 18.4.6: membership in `hypercubeDifferingCoords x y` is exactly
coordinate disagreement between `x` and `y`. -/
private theorem mem_hypercubeDifferingCoords (x y : HypercubeState N) (i : Fin N) :
    i ∈ hypercubeDifferingCoords (N := N) x y ↔ x i ≠ y i := by
  simp [hypercubeDifferingCoords, hypercubeAllCoords_mem (N := N) i]

/-- Helper for Exercise 18.4.6: flipping precisely the differing coordinates carries `x` to `y`.
-/
private theorem hypercubeFlipList_differingCoords_eq (x y : HypercubeState N) :
    hypercubeFlipList (N := N) x (hypercubeDifferingCoords (N := N) x y) = y := by
  ext j
  have hflip :=
    hypercubeFlipList_apply_of_nodup (N := N)
      (l := hypercubeDifferingCoords (N := N) x y)
      ((hypercubeAllCoords_nodup (N := N)).filter _) x j
  rw [hflip]
  by_cases hxy : x j = y j
  · have hj : j ∉ hypercubeDifferingCoords (N := N) x y := by
      simpa [mem_hypercubeDifferingCoords (N := N), hxy] using hxy
    simp [hj, hxy]
  · have hj : j ∈ hypercubeDifferingCoords (N := N) x y := by
      exact (mem_hypercubeDifferingCoords (N := N) x y j).2 hxy
    cases hxj : x j <;> cases hyj : y j <;> simp [hj, hxj, hyj] at hxy ⊢

/-- Helper for Exercise 18.4.6: every prescribed one-coordinate flip has positive singleton mass.
-/
private theorem hypercubeLazyKernel_singleton_pos_flip (x : HypercubeState N) (i : Fin N) :
    0 < (hypercubeLazyKernel N ε) x ({hypercubeFlipAt x i} : Set (HypercubeState N)) := by
  have hweight_pos : 0 < ENNReal.ofReal ((1 - (ε : ℝ)) / N) := by
    apply ENNReal.ofReal_pos.mpr
    refine div_pos (sub_pos.mpr ε.2.2) ?_
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [hypercubeLazyKernel_apply_singleton]
  simp_rw [hypercubeLazyTransitionMatrix]
  rw [if_neg (hypercubeFlipAt_ne_self (N := N) x i)]
  have hsum :
      ∑ j : Fin N,
        (if hypercubeFlipAt x i = hypercubeFlipAt x j then
          ENNReal.ofReal ((1 - (ε : ℝ)) / N)
        else 0) =
        ENNReal.ofReal ((1 - (ε : ℝ)) / N) := by
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun j : Fin N ↦
          if hypercubeFlipAt x i = hypercubeFlipAt x j then
            ENNReal.ofReal ((1 - (ε : ℝ)) / N)
          else 0)
        i (Finset.mem_univ _) (by
          intro j _ hji
          have hij : i ≠ j := by
            intro hij
            exact hji hij.symm
          have hneq : hypercubeFlipAt x i ≠ hypercubeFlipAt x j := by
            intro hijEq
            exact hij ((hypercubeFlipAt_right_injective (N := N) x hijEq))
          simp [hneq]))
  simpa [hsum] using hweight_pos

/-- Helper for Exercise 18.4.6: composing a positive first step with a positive `n`-step singleton
mass yields a positive `(n + 1)`-step singleton mass. -/
private theorem hypercubeLazyKernel_singleton_pos_succ
    {x y z : HypercubeState N} {n : ℕ}
    (hxy : 0 < (hypercubeLazyKernel N ε) x ({y} : Set (HypercubeState N)))
    (hyz : 0 < ((hypercubeLazyKernel N ε) ^ n) y ({z} : Set (HypercubeState N))) :
    0 < ((hypercubeLazyKernel N ε) ^ (n + 1)) x ({z} : Set (HypercubeState N)) := by
  let κ : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε
  have hmeas :
      Measurable fun w : HypercubeState N ↦ (κ ^ n) w ({z} : Set (HypercubeState N)) :=
    Kernel.measurable_coe (κ ^ n) (MeasurableSet.singleton z)
  have hySupport :
      y ∈ Function.support fun w : HypercubeState N ↦ (κ ^ n) w ({z} : Set (HypercubeState N)) := by
    exact hyz.ne'
  have hsupportPos :
      0 < (κ x)
        (Function.support fun w : HypercubeState N ↦ (κ ^ n) w ({z} : Set (HypercubeState N))) :=
    measure_pos_of_superset (Set.singleton_subset_iff.mpr hySupport) hxy.ne'
  -- Proof comment: the composition integral is positive because the support contains the
  -- intermediate state `y` with positive first-step mass.
  rw [show n + 1 = 1 + n by omega]
  rw [Kernel.pow_add_apply_eq_lintegral (κ := κ) 1 n x (MeasurableSet.singleton z)]
  simp only [pow_one]
  rw [MeasureTheory.lintegral_pos_iff_support hmeas]
  exact hsupportPos

/-- Helper for Exercise 18.4.6: following any prescribed flip list yields positive singleton mass
after the corresponding number of steps. -/
private theorem hypercubePositiveSingletonReachabilityOfList
    (x : HypercubeState N) (is : List (Fin N)) :
    ∃ n : ℕ,
      0 < ((hypercubeLazyKernel N ε) ^ n) x
        ({hypercubeFlipList (N := N) x is} : Set (HypercubeState N)) := by
  induction is generalizing x with
  | nil =>
      -- Proof comment: the zero-step kernel is the identity kernel.
      refine ⟨0, ?_⟩
      simpa [pow_zero, hypercubeFlipList] using
        (show 0 < ((Kernel.id : Kernel (HypercubeState N) (HypercubeState N)) x) {x} by
          simp [Kernel.id_apply])
  | cons i is ih =>
      rcases ih (x := hypercubeFlipAt x i) with ⟨n, hn⟩
      refine ⟨n + 1, hypercubeLazyKernel_singleton_pos_succ (N := N) (ε := ε) ?_ hn⟩
      exact hypercubeLazyKernel_singleton_pos_flip (N := N) (ε := ε) x i

/-- Helper for Exercise 18.4.6: every pair of hypercube states is connected by positive singleton
mass after finitely many steps. -/
private theorem hypercubePositiveSingletonReachability (x y : HypercubeState N) :
    ∃ n : ℕ,
      0 < ((hypercubeLazyKernel N ε) ^ n) x ({y} : Set (HypercubeState N)) := by
  rcases
      hypercubePositiveSingletonReachabilityOfList (N := N) (ε := ε) x
        (hypercubeDifferingCoords (N := N) x y) with
    ⟨n, hn⟩
  refine ⟨n, ?_⟩
  simpa [hypercubeFlipList_differingCoords_eq (N := N) x y] using hn

/-- Helper for Exercise 18.4.6: the uniform hypercube law assigns constant singleton mass. -/
private theorem hypercubeUniformDistribution_apply_singleton (x : HypercubeState N) :
    (hypercubeUniformDistribution N : Measure (HypercubeState N)) {x} =
      (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ := by
  -- Proof comment: unfold the uniform distribution and evaluate the underlying PMF on the
  -- singleton `{x}`.
  change ((PMF.uniformOfFintype (HypercubeState N)).toMeasure) {x} =
    (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x), PMF.uniformOfFintype_apply]

-- Proof sketch: for each fixed `x`, there are exactly `N` one-coordinate flips of `x`, each with
-- mass `(1 - ε) / N`, and together with the self-loop mass `ε` these contributions sum to `1`.
/-- The lazy hypercube transition matrix is stochastic. -/
theorem hypercubeLazyTransitionMatrix_isStochastic :
    IsStochasticMatrix (hypercubeLazyTransitionMatrix N ε) := by
  intro x
  -- Proof comment: the row sum splits into the holding contribution at `x` and the `N`
  -- single-coordinate flips, each with weight `((1 - ε) / N)`.
  have hstay :
      ∑ y : HypercubeState N, (if y = x then ENNReal.ofReal (ε : ℝ) else 0) =
        ENNReal.ofReal (ε : ℝ) := by
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun y : HypercubeState N ↦ if y = x then ENNReal.ofReal (ε : ℝ) else 0)
        x (Finset.mem_univ _) (by
          intro y _ hy
          simp [hy]))
  have hflipEntries :
      ∑ y : HypercubeState N,
        ∑ i : Fin N,
          (if y = hypercubeFlipAt x i then ENNReal.ofReal ((1 - (ε : ℝ)) / N) else 0) =
        ∑ i : Fin N, ENNReal.ofReal ((1 - (ε : ℝ)) / N) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simpa using
      (Finset.sum_eq_single_of_mem
        (f := fun y : HypercubeState N ↦
          if y = hypercubeFlipAt x i then ENNReal.ofReal ((1 - (ε : ℝ)) / N) else 0)
        (hypercubeFlipAt x i) (Finset.mem_univ _) (by
          intro y _ hy
          simp [hy]))
  have hflipMass :
      ∑ i : Fin N, ENNReal.ofReal ((1 - (ε : ℝ)) / N) =
        ENNReal.ofReal (1 - (ε : ℝ)) := by
    have hsumReal :
        ∑ i : Fin N, ((1 - (ε : ℝ)) / N : ℝ) = 1 - (ε : ℝ) := by
      have hN : (N : ℝ) ≠ 0 := by
        exact_mod_cast (NeZero.ne N)
      simp [Finset.sum_const, nsmul_eq_mul, hN]
      field_simp [hN]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · simpa [hsumReal]
    · intro i hi
      exact div_nonneg (sub_nonneg.mpr (le_of_lt ε.2.2)) (by positivity)
  rw [tsum_fintype]
  calc
    ∑ y : HypercubeState N, hypercubeLazyTransitionMatrix N ε x y
      = ∑ z : HypercubeState N,
          ((if z = x then ENNReal.ofReal (ε : ℝ) else 0) +
            ∑ i : Fin N,
              if z = hypercubeFlipAt x i then
                ENNReal.ofReal ((1 - (ε : ℝ)) / N)
              else 0) := by
            refine Finset.sum_congr rfl ?_
            intro z hz
            by_cases hzx : z = x
            · subst hzx
              have hflipZero :
                  ∑ i : Fin N,
                    (if z = hypercubeFlipAt z i then
                      ENNReal.ofReal ((1 - (ε : ℝ)) / N)
                    else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro i hi
                have hneq : ¬ z = hypercubeFlipAt z i := by
                  intro h
                  exact hypercubeFlipAt_ne_self (N := N) z i h.symm
                simp [hneq]
              simp [hypercubeLazyTransitionMatrix, hflipZero]
            · simp [hypercubeLazyTransitionMatrix, hzx]
    _ = (∑ y : HypercubeState N, if y = x then ENNReal.ofReal (ε : ℝ) else 0) +
          ∑ y : HypercubeState N,
            ∑ i : Fin N,
              if y = hypercubeFlipAt x i then
                ENNReal.ofReal ((1 - (ε : ℝ)) / N)
              else 0 := by
            rw [Finset.sum_add_distrib]
    _ = ENNReal.ofReal (ε : ℝ) + ENNReal.ofReal (1 - (ε : ℝ)) := by
            rw [hstay, hflipEntries, hflipMass]
    _ = 1 := by
            rw [← ENNReal.ofReal_add]
            · norm_num
            · exact le_of_lt ε.2.1
            · exact sub_nonneg.mpr (le_of_lt ε.2.2)

/-- Helper for Exercise 18.4.6: every column of the lazy hypercube transition matrix has total
mass `1`. -/
private theorem hypercubeLazyTransitionMatrix_columnSum (y : HypercubeState N) :
    ∑ x : HypercubeState N, hypercubeLazyTransitionMatrix N ε x y = 1 := by
  -- Proof comment: symmetry turns the column sum at `y` into the already-known row sum at `y`.
  calc
    ∑ x : HypercubeState N, hypercubeLazyTransitionMatrix N ε x y =
        ∑ x : HypercubeState N, hypercubeLazyTransitionMatrix N ε y x := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hypercubeLazyTransitionMatrix_symm (N := N) (ε := ε) x y]
    _ = 1 := by
          simpa [tsum_fintype] using (hypercubeLazyTransitionMatrix_isStochastic N ε y)

/-- The lazy hypercube kernel is Markov. -/
theorem hypercubeLazyKernel_isMarkovKernel :
    IsMarkovKernel (hypercubeLazyKernel N ε) := by
  simpa [hypercubeLazyKernel] using
    (discreteMatrixKernel_isMarkovKernel
      (hypercubeLazyTransitionMatrix N ε)
      (hypercubeLazyTransitionMatrix_isStochastic N ε))

/-- Helper for Exercise 18.4.6: the lazy hypercube kernel carries the canonical Markov-kernel
instance used by the later finite-measure arguments. -/
private instance hypercubeLazyKernelInstIsMarkovKernel :
    IsMarkovKernel (hypercubeLazyKernel N ε) :=
  hypercubeLazyKernel_isMarkovKernel N ε

/-- Helper for Exercise 18.4.6: every iterate of the lazy hypercube kernel is again Markov. -/
private instance hypercubeLazyKernelPowInstIsMarkovKernel (n : ℕ) :
    IsMarkovKernel (hypercubeLazyKernel N ε ^ n) := by
  induction n with
  | zero =>
      simpa using
        (inferInstance : IsMarkovKernel
          (Kernel.id : Kernel (HypercubeState N) (HypercubeState N)))
  | succ n ih =>
      haveI := ih
      simpa [pow_succ] using
        (inferInstance :
          IsMarkovKernel ((hypercubeLazyKernel N ε ^ n) ∘ₖ hypercubeLazyKernel N ε))

-- Proof sketch: every state has a one-step self-loop of probability `ε > 0`, so each state has a
-- positive return time `1`, which forces period `1`.
/-- For Exercise 18.4.6 (2): the lazy random walk on the hypercube is aperiodic. -/
theorem hypercubeLazyKernel_isAperiodic :
    IsAperiodic (hypercubeLazyKernel N ε) := by
  intro x
  -- Proof comment: the one-step holding move has mass `ε > 0`, so `1` is a positive return time.
  have hself : 1 ∈ positiveTransitionStepSet (hypercubeLazyKernel N ε) x x := by
    rw [mem_positiveTransitionStepSet_iff]
    have hselfMass : 0 < hypercubeLazyKernel N ε x ({x} : Set (HypercubeState N)) := by
      rw [hypercubeLazyKernel_apply_singleton, hypercubeLazyTransitionMatrix, if_pos rfl]
      exact ENNReal.ofReal_pos.mpr ε.2.1
    simpa [pow_one] using hselfMass
  exact Nat.dvd_one.mp
    (statePeriod_dvd_of_mem_positiveTransitionStepSet (hypercubeLazyKernel N ε) x hself)

-- Proof sketch: if `x` and `y` differ in `k` coordinates, successively flip those coordinates.
-- Each prescribed flip has probability `(1 - ε) / N > 0`, so concatenating them gives a
-- positive-probability path from `x` to `y`.
/-- For Exercise 18.4.6 (3): the lazy random walk on the hypercube is irreducible with respect to
counting measure. -/
theorem hypercubeLazyKernel_isIrreducible :
    Kernel.IsIrreducible (Measure.count : Measure (HypercubeState N)) (hypercubeLazyKernel N ε) :=
  by
    classical
    refine ⟨?_⟩
    intro A hA hApos x
    obtain ⟨y, hyA⟩ : A.Nonempty := by
      exact MeasureTheory.nonempty_of_measure_ne_zero (μ := Measure.count) (ne_of_gt hApos)
    rcases hypercubePositiveSingletonReachability (N := N) (ε := ε) x y with ⟨n, hn⟩
    -- Proof comment: a positive singleton path to some chosen `y ∈ A` gives positive mass to `A`.
    refine ⟨n, lt_of_lt_of_le hn ?_⟩
    exact measure_mono (Set.singleton_subset_iff.mpr hyA)

-- Proof sketch: the transition matrix is symmetric, hence doubly stochastic, so averaging over
-- all hypercube vertices is preserved by one step.
/-- For Exercise 18.4.6 (4): the uniform distribution on `{0,1}^N` is invariant for the lazy
hypercube walk. -/
theorem hypercubeUniformDistribution_isInvariant :
    Kernel.Invariant (hypercubeLazyKernel N ε)
      (hypercubeUniformDistribution N : Measure (HypercubeState N)) := by
  rw [Kernel.Invariant]
  refine Measure.ext_of_singleton ?_
  intro y
  -- Proof comment: compare singleton masses and rewrite the kernel action as a finite sum over
  -- the incoming column at `y`.
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _)]
  rw [MeasureTheory.lintegral_fintype]
  simp_rw [hypercubeLazyKernel_apply_singleton]
  have hunif :
      ∀ x : HypercubeState N,
        (hypercubeUniformDistribution N : Measure (HypercubeState N)) {x} =
          (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ :=
    fun x ↦ hypercubeUniformDistribution_apply_singleton (N := N) x
  simp_rw [hunif]
  have hmass :
      ∑ x : HypercubeState N,
        hypercubeLazyTransitionMatrix N ε x y *
          (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ =
        (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ := by
    calc
      ∑ x : HypercubeState N,
        hypercubeLazyTransitionMatrix N ε x y *
          (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ =
          (∑ x : HypercubeState N, hypercubeLazyTransitionMatrix N ε x y) *
            (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ := by
            rw [Finset.sum_mul]
      _ = 1 * (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ := by
            rw [hypercubeLazyTransitionMatrix_columnSum (N := N) (ε := ε)]
      _ = (Fintype.card (HypercubeState N) : ℝ≥0∞)⁻¹ := by simp
  simpa [HypercubeState] using hmass

/-- Helper for Exercise 18.4.6: the Walsh character indexed by the coordinate set `S`. -/
private def hypercubeWalshChar (S : Finset (Fin N)) : HypercubeState N → ℝ :=
  fun x ↦ S.prod fun i ↦ if x i then (-1 : ℝ) else 1

/-- Helper for Exercise 18.4.6: flipping a Boolean sign changes the corresponding Walsh factor by
`-1`. -/
private theorem hypercubeWalshCoord_flip (b : Bool) :
    (if !b then (-1 : ℝ) else 1) = (-1 : ℝ) * (if b then (-1 : ℝ) else 1) := by
  -- Proof comment: check the two Boolean values directly.
  cases b <;> norm_num

/-- Helper for Exercise 18.4.6: flipping coordinate `i` multiplies the Walsh character by `-1`
exactly when `i ∈ S`. -/
private theorem hypercubeWalshChar_flipAt (S : Finset (Fin N))
    (x : HypercubeState N) (i : Fin N) :
    hypercubeWalshChar (N := N) S (hypercubeFlipAt x i) =
      (if i ∈ S then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S x := by
  by_cases hi : i ∈ S
  · -- Proof comment: isolate the flipped coordinate with `insert_erase`; its factor changes by
    -- `-1`, while every remaining factor is unchanged.
    rw [← Finset.insert_erase hi, hypercubeWalshChar, hypercubeWalshChar, Finset.prod_insert,
      Finset.prod_insert]
    · have hprod :
        (S.erase i).prod (fun j ↦ if hypercubeFlipAt x i j then (-1 : ℝ) else 1) =
          (S.erase i).prod (fun j ↦ if x j then (-1 : ℝ) else 1) := by
        refine Finset.prod_congr rfl ?_
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [hypercubeFlipAt, Function.update_of_ne hji]
      have hflipi :
          (if hypercubeFlipAt x i i then (-1 : ℝ) else 1) =
            (-1 : ℝ) * (if x i then (-1 : ℝ) else 1) := by
        simpa [hypercubeFlipAt] using hypercubeWalshCoord_flip (x i)
      rw [hprod, hflipi]
      simp [hi, mul_assoc]
    · exact Finset.notMem_erase _ _
    · exact Finset.notMem_erase _ _
  · -- Proof comment: when `i ∉ S`, every factor of the Walsh product is untouched by the update.
    rw [hypercubeWalshChar, hypercubeWalshChar]
    have hprod :
        S.prod (fun j ↦ if hypercubeFlipAt x i j then (-1 : ℝ) else 1) =
          S.prod (fun j ↦ if x j then (-1 : ℝ) else 1) := by
      refine Finset.prod_congr rfl ?_
      intro j hj
      have hji : j ≠ i := by
        intro hji
        exact hi (hji ▸ hj)
      simp [hypercubeFlipAt, Function.update_of_ne hji]
    rw [hprod]
    simp [hi]

/-- Helper for Exercise 18.4.6: the real-valued flip weights vanish on the diagonal because no
single coordinate flip fixes a hypercube state. -/
private theorem hypercubeFlipWeightReal_selfSum_eq_zero
    (x : HypercubeState N) :
    ∑ i : Fin N,
      (if x = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) = 0 := by
  -- Proof comment: every real-valued flip weight vanishes because a single coordinate flip never
  -- fixes a hypercube state.
  refine Finset.sum_eq_zero ?_
  intro i hi
  have hneq : ¬ x = hypercubeFlipAt x i := by
    intro h
    exact hypercubeFlipAt_ne_self (N := N) x i h.symm
  simp [hneq]

/-- Helper for Exercise 18.4.6: the lazy hypercube kernel acts on a real test function by keeping
mass `ε` at `x` and averaging the `N` coordinate flips with weight `(1 - ε) / N`. -/
private theorem hypercubeLazyKernel_integral_eq_hold_add_flipSum
    (f : HypercubeState N → ℝ) (x : HypercubeState N) :
    ∫ y, f y ∂ hypercubeLazyKernel N ε x =
      (ε : ℝ) * f x + ((1 - (ε : ℝ)) / N) * ∑ i : Fin N, f (hypercubeFlipAt x i) := by
  rw [MeasureTheory.integral_fintype (μ := hypercubeLazyKernel N ε x) (f := f) Integrable.of_finite]
  simp_rw [smul_eq_mul, measureReal_def, hypercubeLazyKernel_apply_singleton]
  -- Proof comment: expand the one-step row into the holding mass and the `N` possible flips.
  calc
    ∑ y : HypercubeState N, (hypercubeLazyTransitionMatrix N ε x y).toReal * f y
      = ∑ y : HypercubeState N,
          (((if y = x then (ε : ℝ) else 0) +
              ∑ i : Fin N,
                if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y) := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          by_cases hyx : y = x
          · subst hyx
            have hflipZeroReal :
                ∑ i : Fin N,
                  (if y = hypercubeFlipAt y i then ((1 - (ε : ℝ)) / N) else 0) = 0 :=
              hypercubeFlipWeightReal_selfSum_eq_zero (N := N) (ε := ε) y
            have hε_nonneg : 0 ≤ (ε : ℝ) := le_of_lt ε.2.1
            calc
              (hypercubeLazyTransitionMatrix N ε y y).toReal * f y = (ε : ℝ) * f y := by
                simp [hypercubeLazyTransitionMatrix, hε_nonneg]
              _ = (((if y = y then (ε : ℝ) else 0) +
                    ∑ i : Fin N,
                      if y = hypercubeFlipAt y i then ((1 - (ε : ℝ)) / N) else 0) * f y) := by
                    simp [hflipZeroReal]
          · have htoReal :
                (∑ i : Fin N,
                  if y = hypercubeFlipAt x i then
                    ENNReal.ofReal ((1 - (ε : ℝ)) / N)
                  else 0).toReal =
                  ∑ i : Fin N,
                    if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0 := by
              have hflipWeight_nonneg : 0 ≤ ((1 - (ε : ℝ)) / N : ℝ) := by
                refine div_nonneg (sub_nonneg.mpr (le_of_lt ε.2.2)) ?_
                exact_mod_cast Nat.zero_le N
              rw [ENNReal.toReal_sum]
              · refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases hyi : y = hypercubeFlipAt x i <;> simp [hyi, hflipWeight_nonneg]
              · intro i hi
                by_cases hyi : y = hypercubeFlipAt x i
                · simp [hyi]
                · simp [hyi]
            calc
              (hypercubeLazyTransitionMatrix N ε x y).toReal * f y =
                  (∑ i : Fin N,
                    if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y := by
                    simp [hypercubeLazyTransitionMatrix, hyx, htoReal]
              _ = (((if y = x then (ε : ℝ) else 0) +
                    ∑ i : Fin N,
                      if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y) := by
                    simp [hyx]
    _ = ∑ y : HypercubeState N, (if y = x then (ε : ℝ) else 0) * f y +
          ∑ y : HypercubeState N,
            (∑ i : Fin N,
              if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro y hy
          ring
    _ = (ε : ℝ) * f x +
          ∑ y : HypercubeState N,
            (∑ i : Fin N,
              if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y := by
          congr 1
          simpa using
            (Finset.sum_eq_single_of_mem x (Finset.mem_univ x)
              (by
                intro y hy hyx
                simp [hyx]))
    _ = (ε : ℝ) * f x +
          ∑ y : HypercubeState N,
            ∑ i : Fin N,
              (if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.sum_mul]
    _ = (ε : ℝ) * f x +
          ∑ i : Fin N,
            ∑ y : HypercubeState N,
              (if y = hypercubeFlipAt x i then ((1 - (ε : ℝ)) / N) else 0) * f y := by
          rw [Finset.sum_comm]
    _ = (ε : ℝ) * f x +
          ∑ i : Fin N, ((1 - (ε : ℝ)) / N) * f (hypercubeFlipAt x i) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using
            (Finset.sum_eq_single_of_mem (hypercubeFlipAt x i)
              (Finset.mem_univ (hypercubeFlipAt x i))
              (by
                intro y hy hyx
                simp [hyx]))
    _ = (ε : ℝ) * f x + ((1 - (ε : ℝ)) / N) * ∑ i : Fin N, f (hypercubeFlipAt x i) := by
          rw [← Finset.mul_sum]

/-- Helper for Exercise 18.4.6: summing the Walsh character over all one-coordinate flips yields
the expected affine factor `(N - 2 * |S|)`. -/
private theorem sum_hypercubeWalshChar_flipAt (S : Finset (Fin N))
    (x : HypercubeState N) :
    ∑ i : Fin N, hypercubeWalshChar (N := N) S (hypercubeFlipAt x i) =
      ((N : ℝ) - 2 * S.card) * hypercubeWalshChar (N := N) S x := by
  have hindicator :
      ∑ i : Fin N, (if i ∈ S then (1 : ℝ) else 0) = S.card := by
    -- Proof comment: the indicator of `S` sums to the number of coordinates contained in `S`.
    simpa [Finset.sum_const, nsmul_eq_mul] using
      (Finset.sum_ite_mem (s := Finset.univ) (t := S) (f := fun _ : Fin N ↦ (1 : ℝ)))
  have hcoeff :
      ∑ i : Fin N, (if i ∈ S then (-1 : ℝ) else 1) = (N : ℝ) - 2 * S.card := by
    -- Proof comment: rewrite each sign as `1 - 2 * 1_S(i)` and sum the indicator.
    calc
      ∑ i : Fin N, (if i ∈ S then (-1 : ℝ) else 1)
        = ∑ i : Fin N, (1 - 2 * (if i ∈ S then (1 : ℝ) else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases his : i ∈ S <;> norm_num [his]
      _ = (∑ i : Fin N, (1 : ℝ)) - 2 * ∑ i : Fin N, (if i ∈ S then (1 : ℝ) else 0) := by
            rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = (N : ℝ) - 2 * S.card := by
            rw [hindicator]
            simp [Finset.sum_const, nsmul_eq_mul]
  -- Proof comment: factor out the common value `χ_S x` after rewriting each flipped character.
  calc
    ∑ i : Fin N, hypercubeWalshChar (N := N) S (hypercubeFlipAt x i)
      = ∑ i : Fin N, (if i ∈ S then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hypercubeWalshChar_flipAt (N := N) (S := S) x i]
    _ = (∑ i : Fin N, (if i ∈ S then (-1 : ℝ) else 1)) *
          hypercubeWalshChar (N := N) S x := by
          rw [Finset.sum_mul]
    _ = ((N : ℝ) - 2 * S.card) * hypercubeWalshChar (N := N) S x := by
          rw [hcoeff]

/-- Helper for Exercise 18.4.6: every Walsh character is an eigenfunction of the lazy hypercube
kernel with eigenvalue `1 - 2 * (1 - ε) * |S| / N`. -/
private theorem hypercubeWalshChar_eigenvalue (S : Finset (Fin N))
    (x : HypercubeState N) :
    ∫ y, hypercubeWalshChar (N := N) S y ∂ hypercubeLazyKernel N ε x =
      (1 - 2 * (1 - (ε : ℝ)) * S.card / N) * hypercubeWalshChar (N := N) S x := by
  let χ : ℝ := hypercubeWalshChar (N := N) S x
  -- Proof comment: the one-step action formula reduces the eigenvalue computation to the finite
  -- Walsh flip sum, which was already collapsed to `(N - 2 * |S|) χ_S(x)`.
  calc
    ∫ y, hypercubeWalshChar (N := N) S y ∂ hypercubeLazyKernel N ε x
      = (ε : ℝ) * hypercubeWalshChar (N := N) S x +
          ((1 - (ε : ℝ)) / N) *
            ∑ i : Fin N, hypercubeWalshChar (N := N) S (hypercubeFlipAt x i) := by
          rw [hypercubeLazyKernel_integral_eq_hold_add_flipSum (N := N) (ε := ε)
            (f := hypercubeWalshChar (N := N) S) x]
    _ = (ε : ℝ) * χ + ((1 - (ε : ℝ)) / N) * (((N : ℝ) - 2 * S.card) * χ) := by
          rw [sum_hypercubeWalshChar_flipAt (N := N) (S := S) x]
    _ = (1 - 2 * (1 - (ε : ℝ)) * S.card / N) * χ := by
          have hN0 : (N : ℝ) ≠ 0 := by
            exact_mod_cast (NeZero.ne N)
          field_simp [hN0]
          ring_nf
    _ = (1 - 2 * (1 - (ε : ℝ)) * S.card / N) * hypercubeWalshChar (N := N) S x := by
          simp [χ]

/-- Helper for Exercise 18.4.6: every Walsh character has absolute value `1`. -/
private theorem hypercubeWalshChar_abs_eq_one (S : Finset (Fin N))
    (x : HypercubeState N) :
    |hypercubeWalshChar (N := N) S x| = 1 := by
  -- Proof comment: each Walsh factor is either `1` or `-1`, so the finite product also has
  -- absolute value `1`.
  induction S using Finset.induction_on with
  | empty =>
      simp [hypercubeWalshChar]
  | insert i T hi hT =>
      have hT' : |∏ j ∈ T, if x j then (-1 : ℝ) else 1| = 1 := by
        simpa [hypercubeWalshChar] using hT
      rw [hypercubeWalshChar, Finset.prod_insert, abs_mul, hT']
      · cases hxi : x i <;> simp [hxi]
      · exact hi

/-- Helper for Exercise 18.4.6: adjoining a fresh coordinate factors the Walsh character by the
corresponding sign at that coordinate. -/
private theorem hypercubeWalshChar_insert {S : Finset (Fin N)} {i : Fin N}
    (hi : i ∉ S) (x : HypercubeState N) :
    hypercubeWalshChar (N := N) (insert i S) x =
      (if x i then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S x := by
  -- Proof comment: isolate the fresh coordinate with `Finset.prod_insert`.
  rw [hypercubeWalshChar, Finset.prod_insert, hypercubeWalshChar]
  exact hi

/-- Helper for Exercise 18.4.6: opposite Boolean values contribute a sign `-1` in the Walsh
product. -/
private theorem hypercubeWalshCoord_mul_of_ne {b c : Bool} (hbc : b ≠ c) :
    (if b then (-1 : ℝ) else 1) * (if c then (-1 : ℝ) else 1) = -1 := by
  -- Proof comment: check the two possible unequal Boolean pairs directly.
  cases b <;> cases c <;> simp at hbc ⊢

/-- Helper for Exercise 18.4.6: summing `χ_S x χ_S y` over all coordinate subsets gives the Walsh
kernel `|E|` on the diagonal and `0` off the diagonal. -/
private theorem hypercubeWalshKernel_overPowerset (x y : HypercubeState N) :
    ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
      hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y =
        if x = y then Fintype.card (HypercubeState N) else 0 := by
  classical
  by_cases hxy : x = y
  · subst hxy
    -- Proof comment: on the diagonal every summand is `1`, so only the number of subsets
    -- remains.
    calc
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
          hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S x =
          ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, (1 : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            have hχ : hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S x = 1 := by
              have habs := hypercubeWalshChar_abs_eq_one (N := N) S x
              have hsq : hypercubeWalshChar (N := N) S x ^ 2 = 1 := by
                nlinarith [sq_abs (hypercubeWalshChar (N := N) S x), habs]
              simpa [pow_two] using hsq
            simpa using hχ
      _ = Fintype.card (((Finset.univ : Finset (Fin N)).powerset : Finset (Finset (Fin N)))) := by
            simp
      _ = Fintype.card (HypercubeState N) := by
            simp [HypercubeState]
      _ = if x = x then Fintype.card (HypercubeState N) else 0 := by simp
  · -- Proof comment: choose a differing coordinate and pair each subset with the subset obtained
    -- by toggling that coordinate; the two paired terms cancel.
    have hcoord : ∃ i : Fin N, x i ≠ y i := by
      by_contra hcoord
      apply hxy
      ext i
      by_contra hi
      exact hcoord ⟨i, hi⟩
    rcases hcoord with ⟨i, hi⟩
    let term : Finset (Fin N) → ℝ := fun S ↦
      hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y
    have hpair :
        ∀ S ∈ (Finset.univ.erase i).powerset, term (insert i S) = -term S := by
      intro S hS
      have hiS : i ∉ S := by
        exact Finset.notMem_of_mem_powerset_of_notMem hS
          (Finset.notMem_erase i (Finset.univ : Finset (Fin N)))
      have hx :
          hypercubeWalshChar (N := N) (insert i S) x =
            (if x i then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S x :=
        hypercubeWalshChar_insert (N := N) hiS x
      have hy :
          hypercubeWalshChar (N := N) (insert i S) y =
            (if y i then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S y :=
        hypercubeWalshChar_insert (N := N) hiS y
      have hsign :
          (if x i then (-1 : ℝ) else 1) * (if y i then (-1 : ℝ) else 1) = -1 :=
        hypercubeWalshCoord_mul_of_ne hi
      calc
        term (insert i S)
          = ((if x i then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S x) *
              ((if y i then (-1 : ℝ) else 1) * hypercubeWalshChar (N := N) S y) := by
                simp [term, hx, hy]
        _ = ((if x i then (-1 : ℝ) else 1) * (if y i then (-1 : ℝ) else 1)) * term S := by
              ring
        _ = -term S := by simp [term, hsign]
    calc
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset, term S
        = ∑ S ∈ (Finset.univ.erase i).powerset, term S +
            ∑ S ∈ (Finset.univ.erase i).powerset, term (insert i S) := by
              rw [← Finset.insert_erase (s := (Finset.univ : Finset (Fin N))) (Finset.mem_univ i)]
              simpa using
                (Finset.sum_powerset_insert
                  (s := Finset.univ.erase i) (a := i) (ha := Finset.notMem_erase _ _) term)
      _ = ∑ S ∈ (Finset.univ.erase i).powerset, term S +
            ∑ S ∈ (Finset.univ.erase i).powerset, (-term S) := by
              refine congrArg ((∑ S ∈ (Finset.univ.erase i).powerset, term S) + ·) ?_
              refine Finset.sum_congr rfl ?_
              intro S hS
              exact hpair S hS
      _ = 0 := by
            simpa using add_neg_cancel (∑ S ∈ (Finset.univ.erase i).powerset, term S)
      _ = if x = y then Fintype.card (HypercubeState N) else 0 := by simp [hxy]

/-- Helper for Exercise 18.4.6: the Walsh eigenvalue relation iterates over all kernel powers. -/
private theorem hypercubeWalshChar_iterate_eigenvalue (S : Finset (Fin N))
    (x : HypercubeState N) :
    ∀ n : ℕ,
      ∫ y, hypercubeWalshChar (N := N) S y ∂((hypercubeLazyKernel N ε) ^ n) x =
        (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n * hypercubeWalshChar (N := N) S x := by
  intro n
  induction n with
  | zero =>
      -- Proof comment: the zero-step kernel is the Dirac mass at the starting state.
      change ∫ y, hypercubeWalshChar (N := N) S y ∂(Kernel.id x) =
        (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ 0 * hypercubeWalshChar (N := N) S x
      simpa [Kernel.id_apply] using
        (MeasureTheory.integral_dirac (f := hypercubeWalshChar (N := N) S) (a := x))
  | succ n ih =>
      let κ : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε
      have hpow :
          hypercubeLazyKernel N ε ^ (n + 1) = κ ∘ₖ (κ ^ n) := by
        simpa [κ] using (pow_succ' κ n)
      rw [hpow]
      letI : IsFiniteMeasure ((κ ∘ₖ (κ ^ n)) x) := by infer_instance
      have hInt :
          Integrable (hypercubeWalshChar (N := N) S) (((κ ∘ₖ (κ ^ n)) x)) := by
        -- Proof comment: the hypercube state space is finite and each Walsh character is bounded
        -- by `1`, so integrability is automatic.
        refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
        exact Filter.Eventually.of_forall fun z ↦ by
          simpa [hypercubeWalshChar_abs_eq_one (N := N) S z]
      -- Proof comment: rewrite the kernel power into the exact composition spelling expected by
      -- `Kernel.integral_comp`, then use the one-step eigenvalue inside the outer integral.
      rw [ProbabilityTheory.Kernel.integral_comp (a := x) (κ := κ ^ n) (η := κ)
        (f := hypercubeWalshChar (N := N) S) hInt]
      calc
        ∫ z, ∫ y, hypercubeWalshChar (N := N) S y ∂κ z ∂(κ ^ n) x
          = ∫ z,
              (1 - 2 * (1 - (ε : ℝ)) * S.card / N) * hypercubeWalshChar (N := N) S z
                ∂(κ ^ n) x := by
                  refine integral_congr_ae ?_
                  exact Filter.Eventually.of_forall fun z ↦
                    hypercubeWalshChar_eigenvalue (N := N) (ε := ε) S z
        _ = (1 - 2 * (1 - (ε : ℝ)) * S.card / N) *
              ∫ z, hypercubeWalshChar (N := N) S z ∂(κ ^ n) x := by
                rw [integral_const_mul]
        _ = (1 - 2 * (1 - (ε : ℝ)) * S.card / N) *
              ((1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n *
                hypercubeWalshChar (N := N) S x) := by
                rw [ih]
        _ = (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ (n + 1) *
              hypercubeWalshChar (N := N) S x := by
                ring_nf

/-- Helper for Exercise 18.4.6: every nontrivial Walsh eigenvalue is bounded by the explicit
convergence factor. -/
private theorem hypercubeWalshEigenvalue_abs_le_convergenceFactor
    (S : Finset (Fin N)) (hS : S.Nonempty) :
    |1 - 2 * (1 - (ε : ℝ)) * S.card / N| ≤ hypercubeLazyConvergenceFactor N ε := by
  have hNpos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hcard_pos : 0 < S.card := Finset.card_pos.mpr hS
  have hcard_le : S.card ≤ N := by
    simpa using (Finset.card_le_univ S)
  by_cases hN : N = 1
  · -- Proof comment: in dimension `1`, the only nonempty Walsh mode is the top mode.
    have hcard : S.card = 1 := by omega
    subst hN
    simp [hypercubeLazyConvergenceFactor, hcard]
  · have hNgt : 1 < N := by omega
    let a : ℝ := 1 - 2 * (1 - (ε : ℝ)) / N
    let b : ℝ := 2 * (ε : ℝ) - 1
    let α : ℝ := ((N : ℝ) - S.card) / ((N : ℝ) - 1)
    let β : ℝ := ((S.card : ℝ) - 1) / ((N : ℝ) - 1)
    have hden_pos : 0 < (N : ℝ) - 1 := by
      have hNgt' : (1 : ℝ) < N := by exact_mod_cast hNgt
      linarith
    have hα_nonneg : 0 ≤ α := by
      refine div_nonneg ?_ hden_pos.le
      exact sub_nonneg.mpr (by exact_mod_cast hcard_le)
    have hβ_nonneg : 0 ≤ β := by
      refine div_nonneg ?_ hden_pos.le
      have hcard_one_le : (1 : ℝ) ≤ S.card := by
        exact_mod_cast Nat.succ_le_of_lt hcard_pos
      linarith
    have hαβ : α + β = 1 := by
      unfold α β
      field_simp [show ((N : ℝ) - 1) ≠ 0 by linarith]
      ring
    have hlin :
        1 - 2 * (1 - (ε : ℝ)) * S.card / N = α * a + β * b := by
      unfold α β a b
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
      have hNm1 : (N : ℝ) - 1 ≠ 0 := by linarith
      field_simp [hN0, hNm1]
      ring
    calc
      |1 - 2 * (1 - (ε : ℝ)) * S.card / N| = |α * a + β * b| := by rw [hlin]
      _ ≤ |α * a| + |β * b| := by simpa using abs_add_le (α * a) (β * b)
      _ = α * |a| + β * |b| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hα_nonneg, abs_of_nonneg hβ_nonneg]
      _ ≤ α * max |a| |b| + β * max |a| |b| := by
            gcongr
            exact le_max_left _ _
            exact le_max_right _ _
      _ = hypercubeLazyConvergenceFactor N ε := by
            rw [show α * max |a| |b| + β * max |a| |b| = (α + β) * max |a| |b| by ring]
            simp [hαβ, hypercubeLazyConvergenceFactor, a, b]

/-- Helper for Exercise 18.4.6: on any finite discrete state space, a real test function bounded
by `1` in norm is integrable against every finite measure. -/
private theorem finiteStateIntegrable_of_norm_le_one
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ := by
  refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
  exact ae_of_all _ hf_bound

/-- Helper for Exercise 18.4.6: specialize the finite-state bounded-integrability lemma to the
hypercube. -/
private theorem integrableHypercube_of_norm_le_one
    {μ : Measure (HypercubeState N)} [IsFiniteMeasure μ] {f : HypercubeState N → ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    Integrable f μ := by
  -- Proof comment: the hypercube is a finite discrete state space, so the generic finite-state
  -- integrability bridge applies verbatim.
  exact finiteStateIntegrable_of_norm_le_one (μ := μ) hf_bound

/-- Helper for Exercise 18.4.6: integrating the singleton indicator against the `n`-step law gives
the corresponding real singleton mass. -/
private theorem hypercubeLazyKernel_indicatorIntegral_eq_singletonReal
    (n : ℕ) (x y : HypercubeState N) :
    ∫ z, (if z = y then (1 : ℝ) else 0) ∂((hypercubeLazyKernel N ε ^ n) x) =
      (((hypercubeLazyKernel N ε ^ n) x).real {y}) := by
  letI : IsFiniteMeasure ((hypercubeLazyKernel N ε ^ n) x) := by infer_instance
  have hInt :
      Integrable (fun z : HypercubeState N ↦ if z = y then (1 : ℝ) else 0)
        ((hypercubeLazyKernel N ε ^ n) x) := by
    refine integrableHypercube_of_norm_le_one (N := N) ?_
    intro z
    by_cases hzy : z = y <;> simp [hzy]
  rw [MeasureTheory.integral_fintype
    (μ := ((hypercubeLazyKernel N ε ^ n) x))
    (f := fun z : HypercubeState N ↦ if z = y then (1 : ℝ) else 0) hInt]
  simp_rw [smul_eq_mul]
  simpa using
    (Finset.sum_eq_single_of_mem
      (f := fun z : HypercubeState N ↦
        (((hypercubeLazyKernel N ε ^ n) x).real {z}) * (if z = y then (1 : ℝ) else 0))
      y (Finset.mem_univ y) (by
        intro z hz hzy
        simp [hzy]))

/-- Helper for Exercise 18.4.6: each Walsh summand is integrable against the `n`-step law of the
lazy hypercube walk. -/
private theorem integrableHypercubeWalshSummand
    (n : ℕ) (x y : HypercubeState N) (S : Finset (Fin N)) :
    Integrable
      (fun z : HypercubeState N ↦
        hypercubeWalshChar (N := N) S z * hypercubeWalshChar (N := N) S y)
      ((hypercubeLazyKernel N ε ^ n) x) := by
  -- Proof comment: every Walsh character has absolute value `1`, so their product is uniformly
  -- bounded by `1`.
  refine integrableHypercube_of_norm_le_one (N := N) ?_
  intro z
  rw [Real.norm_eq_abs, abs_mul,
    hypercubeWalshChar_abs_eq_one (N := N) S z,
    hypercubeWalshChar_abs_eq_one (N := N) S y]
  norm_num

/-- Helper for Exercise 18.4.6: integrating one Walsh summand against the `n`-step law applies
the iterated eigenvalue to the starting state and leaves the terminal Walsh factor untouched. -/
private theorem hypercubeLazyKernel_walshSummand_integral_eq
    (n : ℕ) (x y : HypercubeState N) (S : Finset (Fin N)) :
    ∫ z, hypercubeWalshChar (N := N) S z * hypercubeWalshChar (N := N) S y
        ∂((hypercubeLazyKernel N ε ^ n) x) =
      (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n *
        hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y := by
  -- Proof comment: pull the terminal Walsh factor outside the integral, then use the iterated
  -- Walsh eigenvalue relation for the remaining integral.
  calc
    ∫ z, hypercubeWalshChar (N := N) S z * hypercubeWalshChar (N := N) S y
        ∂((hypercubeLazyKernel N ε ^ n) x)
      = (∫ z, hypercubeWalshChar (N := N) S z ∂((hypercubeLazyKernel N ε ^ n) x)) *
          hypercubeWalshChar (N := N) S y := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (integral_const_mul (r := hypercubeWalshChar (N := N) S y)
                (f := fun z : HypercubeState N ↦ hypercubeWalshChar (N := N) S z))
    _ = ((1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n * hypercubeWalshChar (N := N) S x) *
          hypercubeWalshChar (N := N) S y := by
            rw [hypercubeWalshChar_iterate_eigenvalue (N := N) (ε := ε) S x n]
    _ = (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n *
          hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y := by
            ring

/-- Helper for Exercise 18.4.6: the `n`-step singleton mass admits the explicit Walsh expansion
with the eigenvalue powers of the lazy hypercube walk. -/
private theorem hypercubeLazyKernel_singletonReal_eq_walshSum
    (n : ℕ) (x y : HypercubeState N) :
    (Fintype.card (HypercubeState N) : ℝ) * (((hypercubeLazyKernel N ε ^ n) x).real {y}) =
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
        (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n *
          hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y := by
  calc
    (Fintype.card (HypercubeState N) : ℝ) * (((hypercubeLazyKernel N ε ^ n) x).real {y})
      = (Fintype.card (HypercubeState N) : ℝ) *
          ∫ z, (if z = y then (1 : ℝ) else 0) ∂((hypercubeLazyKernel N ε ^ n) x) := by
            rw [hypercubeLazyKernel_indicatorIntegral_eq_singletonReal (N := N) (ε := ε) n x y]
    _ = ∫ z, (Fintype.card (HypercubeState N) : ℝ) * (if z = y then (1 : ℝ) else 0)
          ∂((hypercubeLazyKernel N ε ^ n) x) := by
            rw [integral_const_mul]
    _ = ∫ z,
          ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
            hypercubeWalshChar (N := N) S z * hypercubeWalshChar (N := N) S y
          ∂((hypercubeLazyKernel N ε ^ n) x) := by
            refine integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun z ↦ by
              by_cases hzy : z = y
              · simpa [hzy] using
                  (hypercubeWalshKernel_overPowerset (N := N) z y).symm
              · simpa [hzy] using
                  (hypercubeWalshKernel_overPowerset (N := N) z y).symm
    _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
          ∫ z, hypercubeWalshChar (N := N) S z * hypercubeWalshChar (N := N) S y
            ∂((hypercubeLazyKernel N ε ^ n) x) := by
            rw [integral_finset_sum _ fun S hS ↦
              integrableHypercubeWalshSummand (N := N) (ε := ε) n x y S]
    _ = ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
          (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n *
            hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y := by
            refine Finset.sum_congr rfl ?_
            intro S hS
            rw [hypercubeLazyKernel_walshSummand_integral_eq (N := N) (ε := ε) n x y S]

/-- Helper for Exercise 18.4.6: the uniform hypercube law has real singleton mass `|E|⁻¹`. -/
private theorem hypercubeUniformDistribution_real_apply_singleton (x : HypercubeState N) :
    (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {x} =
      (Fintype.card (HypercubeState N) : ℝ)⁻¹ := by
  rw [measureReal_def, hypercubeUniformDistribution_apply_singleton (N := N) x]
  simp

/-- Helper for Exercise 18.4.6: the Walsh summand occurring in the singleton-mass expansion of
the lazy hypercube walk. -/
private def hypercubeWalshSingletonSummand
    (n : ℕ) (x y : HypercubeState N) (S : Finset (Fin N)) : ℝ :=
  (1 - 2 * (1 - (ε : ℝ)) * S.card / N) ^ n *
    hypercubeWalshChar (N := N) S x * hypercubeWalshChar (N := N) S y

/-- Helper for Exercise 18.4.6: after removing the empty Walsh mode, the scaled singleton
deviation is exactly the sum over the nonempty coordinate subsets. -/
private theorem hypercubeLazyKernel_singletonDeviation_scaled_eq_nonemptyWalshSum
    (n : ℕ) (x y : HypercubeState N) :
    (Fintype.card (HypercubeState N) : ℝ) *
        ((((hypercubeLazyKernel N ε ^ n) x).real {y}) -
          (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y}) =
      ∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
        hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S := by
  have hcard_ne : (Fintype.card (HypercubeState N) : ℝ) ≠ 0 := by
    positivity
  have hsum_split :
      ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
          hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S =
        ∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
            hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S +
          ∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter (fun S ↦ ¬ S.Nonempty),
            hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (s := (Finset.univ : Finset (Fin N)).powerset)
        (p := Finset.Nonempty)
        (f := hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y)).symm
  have hempty :
      ∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter (fun S ↦ ¬ S.Nonempty),
          hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S = 1 := by
    have hemptySet :
        ((Finset.univ : Finset (Fin N)).powerset).filter (fun S ↦ ¬ S.Nonempty) = {∅} := by
      ext S
      simp [Finset.not_nonempty_iff_eq_empty]
    rw [hemptySet]
    simp [hypercubeWalshSingletonSummand, hypercubeWalshChar]
  -- Proof comment: the Walsh expansion contains one constant empty-mode contribution `1`; after
  -- subtracting the uniform singleton mass, only the nonempty modes remain.
  calc
    (Fintype.card (HypercubeState N) : ℝ) *
        ((((hypercubeLazyKernel N ε ^ n) x).real {y}) -
          (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y})
      = (Fintype.card (HypercubeState N) : ℝ) * (((hypercubeLazyKernel N ε ^ n) x).real {y}) - 1 := by
          rw [hypercubeUniformDistribution_real_apply_singleton (N := N) y]
          field_simp [hcard_ne]
    _ =
        ∑ S ∈ (Finset.univ : Finset (Fin N)).powerset,
          hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S - 1 := by
          simpa [hypercubeWalshSingletonSummand] using
            hypercubeLazyKernel_singletonReal_eq_walshSum (N := N) (ε := ε) n x y
    _ =
        ∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
          hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S := by
          rw [hsum_split, hempty]
          ring

/-- Helper for Exercise 18.4.6: the sum of the nonempty Walsh modes is bounded by the cardinality
of the hypercube times the explicit convergence factor. -/
private theorem hypercubeWalshSingletonSummand_nonempty_sum_bound
    (n : ℕ) (x y : HypercubeState N) :
    |∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
        hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S|
      ≤ (Fintype.card (HypercubeState N) : ℝ) *
          hypercubeLazyConvergenceFactor N ε ^ n := by
  have hrate_nonneg : 0 ≤ hypercubeLazyConvergenceFactor N ε := by
    exact le_trans (abs_nonneg _) (le_max_left _ _)
  calc
    |∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
        hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S|
      ≤ ∑ S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
          |hypercubeWalshSingletonSummand (N := N) (ε := ε) n x y S| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ ((Finset.univ : Finset (Fin N)).powerset).filter Finset.Nonempty,
          hypercubeLazyConvergenceFactor N ε ^ n := by
          refine Finset.sum_le_sum ?_
          intro S hS
          rw [hypercubeWalshSingletonSummand, abs_mul, abs_mul,
            hypercubeWalshChar_abs_eq_one (N := N) S x,
            hypercubeWalshChar_abs_eq_one (N := N) S y, mul_one, mul_one, abs_pow]
          have hnonempty : S.Nonempty := (Finset.mem_filter.mp hS).2
          exact pow_le_pow_left₀ (abs_nonneg _)
            (hypercubeWalshEigenvalue_abs_le_convergenceFactor
              (N := N) (ε := ε) S hnonempty) _
    _ = (((Finset.univ : Finset (Fin N)).powerset.filter Finset.Nonempty).card : ℝ) *
          hypercubeLazyConvergenceFactor N ε ^ n := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
    _ ≤ (Fintype.card (HypercubeState N) : ℝ) *
          hypercubeLazyConvergenceFactor N ε ^ n := by
          have hcard_le :
              (((Finset.univ : Finset (Fin N)).powerset.filter Finset.Nonempty).card : ℝ) ≤
                (Fintype.card (HypercubeState N) : ℝ) := by
            calc
              (((Finset.univ : Finset (Fin N)).powerset.filter Finset.Nonempty).card : ℝ)
                  ≤ (((Finset.univ : Finset (Fin N)).powerset).card : ℝ) := by
                    exact_mod_cast
                      (Finset.card_filter_le
                        ((Finset.univ : Finset (Fin N)).powerset) Finset.Nonempty)
              _ = (Fintype.card (HypercubeState N) : ℝ) := by
                    simp [HypercubeState]
          have hpownonneg : 0 ≤ hypercubeLazyConvergenceFactor N ε ^ n := by
            exact pow_nonneg hrate_nonneg _
          nlinarith

/-- Helper for Exercise 18.4.6: scaling by the hypercube cardinality converts the singleton
deviation bound into the same scaled convergence-factor bound. -/
private theorem hypercubeLazyKernel_singletonDeviation_scaled_bound
    (n : ℕ) (x y : HypercubeState N) :
    (Fintype.card (HypercubeState N) : ℝ) *
        |((hypercubeLazyKernel N ε ^ n) x).real {y} -
          (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y}|
      ≤ (Fintype.card (HypercubeState N) : ℝ) *
          hypercubeLazyConvergenceFactor N ε ^ n := by
  have hcard_pos : 0 < (Fintype.card (HypercubeState N) : ℝ) := by
    positivity
  have habs :
      (Fintype.card (HypercubeState N) : ℝ) *
          |((hypercubeLazyKernel N ε ^ n) x).real {y} -
            (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y}| =
        |(Fintype.card (HypercubeState N) : ℝ) *
          (((hypercubeLazyKernel N ε ^ n) x).real {y} -
            (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y})| := by
    rw [abs_mul, abs_of_nonneg hcard_pos.le]
  -- Proof comment: the previous identity rewrites the scaled deviation as a nonempty Walsh sum,
  -- and the Walsh-mode bound controls that sum.
  rw [habs, hypercubeLazyKernel_singletonDeviation_scaled_eq_nonemptyWalshSum (N := N) (ε := ε) n x y]
  simpa [abs_of_nonneg hcard_pos.le] using
    hypercubeWalshSingletonSummand_nonempty_sum_bound (N := N) (ε := ε) n x y

/-- Helper for Exercise 18.4.6: from a fixed starting state, every singleton mass differs from the
uniform singleton mass by at most `hypercubeLazyConvergenceFactor N ε ^ n`. -/
private theorem hypercubeLazyKernel_singleton_uniformBound
    (n : ℕ) (x y : HypercubeState N) :
    |(((hypercubeLazyKernel N ε ^ n) x).real {y} -
        (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y})|
      ≤ hypercubeLazyConvergenceFactor N ε ^ n := by
  have hcard_pos : 0 < (Fintype.card (HypercubeState N) : ℝ) := by
    positivity
  have hscaled :=
    hypercubeLazyKernel_singletonDeviation_scaled_bound (N := N) (ε := ε) n x y
  -- Proof comment: divide the scaled estimate by the positive hypercube cardinality.
  nlinarith

/-- Helper for Exercise 18.4.6: on a finite discrete state space, a row-wise singleton-gap bound
for a Markov kernel persists after averaging over an initial law. -/
private theorem finiteStateCompMeasure_realSingleton_eq_sum
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (μ : ProbabilityMeasure E) (y : E) :
    (κ ∘ₘ (μ : Measure E)).real {y} =
      ∑ x : E, (μ : Measure E).real {x} * (κ x).real {y} := by
  have hsingleton_le_one : ∀ x : E, κ x {y} ≤ 1 := by
    intro x
    simpa using (measure_mono (by simp : ({y} : Set E) ⊆ Set.univ) : κ x {y} ≤ κ x Set.univ)
  have hsingleton_finite : ∀ᵐ x ∂(μ : Measure E), κ x {y} < ∞ := by
    exact ae_of_all _ fun x ↦ lt_of_le_of_lt (hsingleton_le_one x) (by simp)
  have hrow_integrable : Integrable (fun x : E ↦ (κ x).real {y}) (μ : Measure E) := by
    -- Proof comment: singleton masses stay in `[0,1]`, so the row-mass function is integrable.
    refine finiteStateIntegrable_of_norm_le_one (μ := (μ : Measure E)) ?_
    intro x
    simpa [Real.norm_eq_abs, abs_of_nonneg MeasureTheory.measureReal_nonneg] using
      (MeasureTheory.measureReal_le_one (μ := κ x) (s := ({y} : Set E)))
  -- Proof comment: evaluate the composed measure on `{y}` and convert the resulting integral into
  -- a finite sum over the discrete state space.
  calc
    (κ ∘ₘ (μ : Measure E)).real {y}
      = (∫⁻ x, κ x {y} ∂(μ : Measure E)).toReal := by
          rw [measureReal_def, Measure.bind_apply (measurableSet_singleton y)
            (Kernel.aemeasurable _)]
    _ = ∫ x, (κ x).real {y} ∂(μ : Measure E) := by
          symm
          simpa [measureReal_def] using
            (integral_toReal (Measurable.of_discrete.aemeasurable) hsingleton_finite)
    _ = ∑ x : E, (μ : Measure E).real {x} * (κ x).real {y} := by
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_fintype
              (μ := (μ : Measure E)) (f := fun x : E ↦ (κ x).real {y}) hrow_integrable)

/-- Helper for Exercise 18.4.6: the real singleton masses of a probability measure on a finite
discrete state space sum to `1`. -/
private theorem finiteStateProbabilityMeasure_realSingleton_sum_eq_one
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (μ : ProbabilityMeasure E) :
    ∑ x : E, (μ : Measure E).real {x} = 1 := by
  -- Proof comment: on a finite discrete space, integrating the constant function `1` is the same
  -- as summing the singleton masses.
  calc
    ∑ x : E, (μ : Measure E).real {x}
      = ∫ x, (1 : ℝ) ∂(μ : Measure E) := by
          symm
          simpa [smul_eq_mul] using
            (MeasureTheory.integral_fintype
              (μ := (μ : Measure E)) (f := fun _ : E ↦ (1 : ℝ)) (integrable_const 1))
    _ = 1 := by simp

/-- Helper for Exercise 18.4.6: subtracting the target singleton mass from the convex combination
of row singleton masses distributes through the same finite weights. -/
private theorem finiteStateCompMeasure_singletonGap_sum_eq
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) (μ π : ProbabilityMeasure E) (y : E) :
    (∑ x : E, (μ : Measure E).real {x} * (κ x).real {y}) - (π : Measure E).real {y} =
      ∑ x : E, (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y}) := by
  have hweights_sum :
      ∑ x : E, (μ : Measure E).real {x} = 1 :=
    finiteStateProbabilityMeasure_realSingleton_sum_eq_one (μ := μ)
  -- Proof comment: rewrite the target singleton mass using the same weights and distribute the
  -- subtraction termwise across the finite sum.
  calc
    (∑ x : E, (μ : Measure E).real {x} * (κ x).real {y}) - (π : Measure E).real {y}
      = (∑ x : E, (μ : Measure E).real {x} * (κ x).real {y}) -
          ∑ x : E, (μ : Measure E).real {x} * (π : Measure E).real {y} := by
            have hconst :
                ∑ x : E, (μ : Measure E).real {x} * (π : Measure E).real {y} =
                  (π : Measure E).real {y} * ∑ x : E, (μ : Measure E).real {x} := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
            rw [hconst, hweights_sum, mul_one]
    _ = ∑ x : E,
          ((μ : Measure E).real {x} * (κ x).real {y} -
            (μ : Measure E).real {x} * (π : Measure E).real {y}) := by
            rw [← Finset.sum_sub_distrib]
    _ = ∑ x : E, (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y}) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            ring

private theorem finiteStateCompMeasure_singletonGap_le_of_rowBound
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (κ : Kernel E E) [IsMarkovKernel κ] (μ π : ProbabilityMeasure E) (A : ℝ)
    (hpoint :
      ∀ x y : E, |((κ x).real {y} - (π : Measure E).real {y})| ≤ A) :
    ∀ y : E, |((κ ∘ₘ (μ : Measure E)).real {y} - (π : Measure E).real {y})| ≤ A := by
  intro y
  -- Proof comment: the evolved singleton deviation is a convex combination of the row deviations,
  -- so the row-wise bound survives averaging.
  calc
    |((κ ∘ₘ (μ : Measure E)).real {y}) - (π : Measure E).real {y}|
      = |∑ x : E, (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y})| := by
          rw [finiteStateCompMeasure_realSingleton_eq_sum (κ := κ) (μ := μ) y,
            finiteStateCompMeasure_singletonGap_sum_eq (κ := κ) (μ := μ) (π := π) y]
    _ ≤ ∑ x : E, |(μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y})| := by
          simpa using
            (Finset.abs_sum_le_sum_abs
              (s := (Finset.univ : Finset E))
              (f := fun x : E ↦
                (μ : Measure E).real {x} * ((κ x).real {y} - (π : Measure E).real {y})))
    _ = ∑ x : E, (μ : Measure E).real {x} * |(κ x).real {y} - (π : Measure E).real {y}| := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          rw [abs_mul, abs_of_nonneg MeasureTheory.measureReal_nonneg]
    _ ≤ ∑ x : E, (μ : Measure E).real {x} * A := by
          refine Finset.sum_le_sum ?_
          intro x hx
          gcongr
          exact hpoint x y
    _ = A * ∑ x : E, (μ : Measure E).real {x} := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
    _ = A := by
          rw [finiteStateProbabilityMeasure_realSingleton_sum_eq_one (μ := μ), mul_one]

/-- Helper for Exercise 18.4.6: on a finite discrete state space, a uniform singleton-gap bound
implies a total-variation bound through the chapter-owner dual formula. -/
private theorem finiteStateIntegralDiff_eq_singletonSum
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (ρ π : ProbabilityMeasure E) {f : E → ℝ}
    (hρ_int : Integrable f (ρ : Measure E)) (hπ_int : Integrable f (π : Measure E)) :
    ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E) =
      ∑ y : E, (((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y) := by
  -- Proof comment: on a finite discrete space, both expectations are finite sums over singleton
  -- masses, so their difference is the corresponding termwise difference.
  rw [MeasureTheory.integral_fintype (μ := (ρ : Measure E)) (f := f) hρ_int,
    MeasureTheory.integral_fintype (μ := (π : Measure E)) (f := f) hπ_int]
  simp_rw [smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro y hy
  ring

/-- Helper for Exercise 18.4.6: every bounded measurable test function is controlled by the
uniform singleton-gap estimate. -/
private theorem finiteStateBoundedTestFunction_gap_le
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (ρ π : ProbabilityMeasure E) (A : ℝ)
    (hsingleton :
      ∀ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| ≤ A)
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1) :
    ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E) ≤ (Fintype.card E : ℝ) * A := by
  have hρ_int : Integrable f (ρ : Measure E) :=
    finiteStateIntegrable_of_norm_le_one (μ := (ρ : Measure E)) hf_bound
  have hπ_int : Integrable f (π : Measure E) :=
    finiteStateIntegrable_of_norm_le_one (μ := (π : Measure E)) hf_bound
  -- Proof comment: expand the integral difference into a singleton sum, then use `‖f‖ ≤ 1` and
  -- the uniform pointwise gap bound.
  calc
    ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E)
      = ∑ y : E, (((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y) := by
          rw [finiteStateIntegralDiff_eq_singletonSum (ρ := ρ) (π := π) hρ_int hπ_int]
    _ ≤ ∑ y : E, |(((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y)| := by
          refine le_trans (le_abs_self _) ?_
          simpa using
            (Finset.abs_sum_le_sum_abs
              (s := (Finset.univ : Finset E))
              (f := fun y : E ↦ ((ρ : Measure E).real {y} - (π : Measure E).real {y}) * f y))
    _ = ∑ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| * ‖f y‖ := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [abs_mul, Real.norm_eq_abs]
    _ ≤ ∑ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| * 1 := by
          refine Finset.sum_le_sum ?_
          intro y hy
          gcongr
          exact hf_bound y
    _ ≤ ∑ y : E, A * 1 := by
          refine Finset.sum_le_sum ?_
          intro y hy
          gcongr
          exact hsingleton y
    _ = (Fintype.card E : ℝ) * A := by
          simp [mul_comm]

private theorem finiteStateTotalVariation_le_of_singletonGap
    {E : Type*} [Fintype E] [MeasurableSpace E] [DiscreteMeasurableSpace E]
    (ρ π : ProbabilityMeasure E) (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hsingleton :
      ∀ y : E, |((ρ : Measure E).real {y} - (π : Measure E).real {y})| ≤ A) :
    totalVariationDistance ρ π ≤ (Fintype.card E : ℝ) * A / 2 := by
  let S : Set ℝ := {r : ℝ | ∃ f : E → ℝ,
    Measurable f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      r = ∫ x, f x ∂(ρ : Measure E) - ∫ x, f x ∂(π : Measure E)}
  have hzero_mem : 0 ∈ S := by
    -- Proof comment: the zero function is always admissible in the dual description.
    exact ⟨fun _ : E ↦ 0, measurable_const, (by intro x; simp), by simp [S]⟩
  have hupper : ∀ r ∈ S, r ≤ (Fintype.card E : ℝ) * A := by
    intro r hr
    rcases hr with ⟨f, hf_meas, hf_bound, rfl⟩
    exact finiteStateBoundedTestFunction_gap_le
      (ρ := ρ) (π := π) (A := A) hsingleton hf_meas hf_bound
  have hS_nonempty : S.Nonempty := ⟨0, hzero_mem⟩
  have hsSup_le : sSup S ≤ (Fintype.card E : ℝ) * A := by
    exact csSup_le hS_nonempty fun r hr ↦ hupper r hr
  -- Proof comment: the dual formula divides the supremum of admissible test-function gaps by `2`.
  rw [totalVariationDistance_eq_sSup_bounded_measurable]
  change sSup S / 2 ≤ (Fintype.card E : ℝ) * A / 2
  nlinarith

/-- Helper for Exercise 18.4.6: averaging the Dirac-start singleton bound over the initial law
preserves the same bound for the evolved law. -/
private theorem hypercubeLazyKernel_compMeasure_singleton_uniformBound
    (μ : ProbabilityMeasure (HypercubeState N)) (n : ℕ) (y : HypercubeState N) :
    |((((hypercubeLazyKernel N ε ^ n) ∘ₘ (μ : Measure (HypercubeState N))).real {y}) -
        (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y})|
      ≤ hypercubeLazyConvergenceFactor N ε ^ n := by
  -- Route correction: replace the hypercube-specific averaging proof by the generic finite-state
  -- singleton-gap bridge so the endgame only depends on the Walsh row bound.
  let κn : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε ^ n
  let _ : IsMarkovKernel κn := by
    dsimp [κn]
    infer_instance
  simpa [κn] using
    (finiteStateCompMeasure_singletonGap_le_of_rowBound
      (κ := κn)
      (μ := μ)
      (π := hypercubeUniformDistribution N)
      (A := hypercubeLazyConvergenceFactor N ε ^ n)
      (hpoint := fun x z ↦ hypercubeLazyKernel_singleton_uniformBound (N := N) (ε := ε) n x z)
      y)

/-- Helper for Exercise 18.4.6: on the finite hypercube, a uniform singleton-mass estimate yields
a total-variation estimate by testing against bounded measurable functions. -/
private theorem hypercube_totalVariation_le_of_singletonUniformBound
    (ρ π : ProbabilityMeasure (HypercubeState N)) (A : ℝ) (hA_nonneg : 0 ≤ A)
    (hsingleton :
      ∀ y : HypercubeState N,
        |((ρ : Measure (HypercubeState N)).real {y} -
            (π : Measure (HypercubeState N)).real {y})| ≤ A) :
    totalVariationDistance ρ π ≤ (Fintype.card (HypercubeState N) : ℝ) * A / 2 := by
  -- Route correction: use the generic finite-state TV bridge instead of re-expanding the dual
  -- formula in a hypercube-specific proof block.
  simpa using
    (finiteStateTotalVariation_le_of_singletonGap
      (ρ := ρ)
      (π := π)
      (A := A)
      hA_nonneg
      hsingleton)

-- Proof sketch: diagonalize the walk by the Walsh basis on `{0,1}^N`, use the resulting explicit
-- singleton-mass expansion to bound every point mass by the largest nontrivial Walsh eigenvalue,
-- and then translate that finite-state pointwise estimate into total variation.
/-- Exercise 18.4.6 (5): the lazy hypercube walk converges exponentially fast to the uniform
distribution in total variation, with rate given by the largest nontrivial eigenvalue modulus. -/
theorem hypercubeLazyKernel_totalVariation_exponential_bound :
    let _ : IsMarkovKernel (hypercubeLazyKernel N ε) := hypercubeLazyKernel_isMarkovKernel N ε
    ∃ C : ℝ,
      0 ≤ C ∧
        ∀ n : ℕ,
          ∀ μ : ProbabilityMeasure (HypercubeState N),
            let κn : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε ^ n
            totalVariationDistance
              (⟨κn ∘ₘ (μ : Measure (HypercubeState N)),
                inferInstance⟩ : ProbabilityMeasure (HypercubeState N))
              (hypercubeUniformDistribution N) ≤
            C * hypercubeLazyConvergenceFactor N ε ^ n := by
  refine ⟨(Fintype.card (HypercubeState N) : ℝ) / 2, by positivity, ?_⟩
  intro n μ
  let κn : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε ^ n
  let νn : ProbabilityMeasure (HypercubeState N) :=
    ⟨κn ∘ₘ (μ : Measure (HypercubeState N)), inferInstance⟩
  have hrate_nonneg : 0 ≤ hypercubeLazyConvergenceFactor N ε ^ n := by
    exact pow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _
  have hsingletons :
      ∀ y : HypercubeState N,
        |(((νn : ProbabilityMeasure (HypercubeState N)) : Measure (HypercubeState N)).real {y} -
            (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y})|
          ≤ hypercubeLazyConvergenceFactor N ε ^ n := by
    intro y
    simpa [νn, κn] using
      hypercubeLazyKernel_compMeasure_singleton_uniformBound (N := N) (ε := ε) μ n y
  have htv :
      totalVariationDistance
          νn
          (hypercubeUniformDistribution N)
        ≤ (Fintype.card (HypercubeState N) : ℝ) *
            (hypercubeLazyConvergenceFactor N ε ^ n) / 2 :=
    hypercube_totalVariation_le_of_singletonUniformBound (N := N)
      (ρ := νn)
      (π := hypercubeUniformDistribution N)
      (A := hypercubeLazyConvergenceFactor N ε ^ n) hrate_nonneg hsingletons
  calc
    totalVariationDistance
        νn
        (hypercubeUniformDistribution N)
      ≤ (Fintype.card (HypercubeState N) : ℝ) *
          (hypercubeLazyConvergenceFactor N ε ^ n) / 2 := htv
    _ = ((Fintype.card (HypercubeState N) : ℝ) / 2) *
          hypercubeLazyConvergenceFactor N ε ^ n := by
          ring

/-- Helper for Exercise 18.4.6: the explicit hypercube convergence factor is strictly less than
`1`. -/
private theorem hypercubeLazyConvergenceFactor_lt_one :
    hypercubeLazyConvergenceFactor N ε < 1 := by
  have hε0 : 0 < (ε : ℝ) := ε.2.1
  have hε1 : (ε : ℝ) < 1 := ε.2.2
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNge1 : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N))
  have hsub_nonneg : 0 ≤ 1 - (ε : ℝ) := by
    linarith
  have hdiv_pos : 0 < (1 - (ε : ℝ)) / N := by
    exact div_pos (sub_pos.mpr hε1) hNpos
  have hdiv_lt_one : (1 - (ε : ℝ)) / N < 1 := by
    have hdiv_le_sub : (1 - (ε : ℝ)) / N ≤ 1 - (ε : ℝ) := by
      calc
        (1 - (ε : ℝ)) / N = (1 - (ε : ℝ)) * ((1 : ℝ) / N) := by ring
        _ ≤ (1 - (ε : ℝ)) * 1 := by
              gcongr
              have hone_div_le : (1 : ℝ) / N ≤ 1 := by
                have hNne : (N : ℝ) ≠ 0 := by positivity
                field_simp [hNne]
                linarith
              exact hone_div_le
        _ = 1 - (ε : ℝ) := by ring
    have hsub_lt_one : 1 - (ε : ℝ) < 1 := by
      linarith
    exact lt_of_le_of_lt hdiv_le_sub hsub_lt_one
  have hfirst : |1 - 2 * (1 - (ε : ℝ)) / N| < 1 := by
    let a : ℝ := (1 - (ε : ℝ)) / N
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (NeZero.ne N)
    have hfirst_eq : 1 - 2 * (1 - (ε : ℝ)) / N = 1 - 2 * a := by
      unfold a
      field_simp [hN0]
    have ha_pos : 0 < a := hdiv_pos
    have ha_lt_one : a < 1 := hdiv_lt_one
    have hleft : -1 < 1 - 2 * a := by
      nlinarith
    have hright : 1 - 2 * a < 1 := by
      nlinarith
    rw [hfirst_eq]
    exact abs_lt.mpr ⟨hleft, hright⟩
  have hsecond : |2 * (ε : ℝ) - 1| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  exact max_lt hfirst hsecond

-- Proof sketch: invariance forces every `n`-step law started from `μ` to remain equal to `μ`.
-- The singleton-mass convergence bound then shows every singleton mass of `μ` matches the
-- corresponding uniform singleton mass, hence the measures are equal on the finite hypercube.
/-- Any invariant distribution of the lazy hypercube walk is the uniform distribution. -/
theorem hypercubeLazyKernel_invariantDistribution_eq_uniform
    (μ : ProbabilityMeasure (HypercubeState N))
    (hμ : Kernel.Invariant (hypercubeLazyKernel N ε) (μ : Measure (HypercubeState N))) :
    μ = hypercubeUniformDistribution N := by
  let κ : Kernel (HypercubeState N) (HypercubeState N) := hypercubeLazyKernel N ε
  have hrate_lt : hypercubeLazyConvergenceFactor N ε < 1 :=
    hypercubeLazyConvergenceFactor_lt_one (N := N) (ε := ε)
  have hpowInvariant :
      ∀ n : ℕ, Kernel.Invariant (κ ^ n) (μ : Measure (HypercubeState N)) := by
    intro n
    induction n with
    | zero =>
        change (Kernel.id : Kernel (HypercubeState N) (HypercubeState N)) ∘ₘ
            (μ : Measure (HypercubeState N)) = (μ : Measure (HypercubeState N))
        exact Measure.id_comp (μ := (μ : Measure (HypercubeState N)))
    | succ n ih =>
        simpa [κ, pow_succ'] using Kernel.Invariant.comp hμ ih
  have hsingletonReal :
      ∀ y : HypercubeState N,
        (μ : Measure (HypercubeState N)).real {y} =
          (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y} := by
    intro y
    by_contra hy
    have hdiff_pos :
        0 <
          |((μ : Measure (HypercubeState N)).real {y} -
              (hypercubeUniformDistribution N : Measure (HypercubeState N)).real {y})| := by
      exact abs_pos.mpr (sub_ne_zero.mpr hy)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hdiff_pos hrate_lt
    have hbound :=
      hypercubeLazyKernel_compMeasure_singleton_uniformBound
        (N := N) (ε := ε) μ n y
    have hpowEq :
        (κ ^ n) ∘ₘ (μ : Measure (HypercubeState N)) = (μ : Measure (HypercubeState N)) := by
      simpa [Kernel.Invariant] using hpowInvariant n
    rw [hpowEq] at hbound
    exact (not_lt_of_ge hbound) hn
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_singleton fun y ↦ ?_
  have hreal := hsingletonReal y
  rw [measureReal_def, measureReal_def] at hreal
  exact
    (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top (μ : Measure (HypercubeState N)) {y})
      (measure_ne_top (hypercubeUniformDistribution N : Measure (HypercubeState N)) {y})).mp hreal

end LazyHypercube

end ProbabilityTheory

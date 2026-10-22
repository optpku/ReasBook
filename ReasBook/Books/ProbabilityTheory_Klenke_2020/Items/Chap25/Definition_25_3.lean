/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-
Definition 25.3 is `source-facing`: it defines the elementary Brownian Itô integral on the
canonical owner `PredictableSimpleProcess ℱ` from Definition 25.2. The namespace
`PredictableStepRepresentation` is only the `bridge/view` layer that records the explicit finite
increment sum for a chosen predictable-step presentation and proves that this formula depends only
on the underlying owner process.
-/

namespace PredictableStepRepresentation

variable {ℱ : ContinuousFiltration}

/-- The stopped Itô sum attached to a predictable-step representation. This is the
representation-level formula underlying Definition 25.3. -/
def brownianElementaryIntegral (H : PredictableStepRepresentation ℱ) (W : Process) : Process :=
  fun t ω ↦
    ∑ i : Fin H.n,
      H.coeff i ω *
        (W (min (H.times i.succ) t) ω - W (min (H.times i.castSucc) t) ω)

/-- The terminal Itô sum attached to a predictable-step representation, obtained by evaluating
the stopped integral at the final partition time. -/
def brownianElementaryIntegralAtInfinity
    (H : PredictableStepRepresentation ℱ) (W : Process) : Ω → ℝ :=
  PredictableStepRepresentation.brownianElementaryIntegral H W (H.times (Fin.last H.n))

/-- Evaluating the stopped elementary Brownian integral gives the defining truncated increment
sum. -/
@[simp] theorem brownianElementaryIntegral_apply {ℱ : ContinuousFiltration}
    (H : PredictableStepRepresentation ℱ) (W : Process) (t : NNReal) (ω : Ω) :
    PredictableStepRepresentation.brownianElementaryIntegral H W t ω =
      ∑ i : Fin H.n,
        H.coeff i ω *
          (W (min (H.times i.succ) t) ω - W (min (H.times i.castSucc) t) ω) :=
  rfl

/-- Evaluating the terminal elementary Brownian integral gives the full increment sum over the
partition of `H`. -/
@[simp] theorem brownianElementaryIntegralAtInfinity_apply
    (H : PredictableStepRepresentation ℱ) (W : Process) (ω : Ω) :
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W ω =
      ∑ i : Fin H.n,
        H.coeff i ω * (W (H.times i.succ) ω - W (H.times i.castSucc) ω) := by
  -- At the last partition time, every truncation `min (H.times ·) (H.times last)` collapses to
  -- the corresponding partition endpoint.
  rw [PredictableStepRepresentation.brownianElementaryIntegralAtInfinity,
    PredictableStepRepresentation.brownianElementaryIntegral_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi_succ_le_last : i.succ ≤ Fin.last H.n := Fin.le_last i.succ
  have hi_castSucc_le_last : i.castSucc ≤ Fin.last H.n := Fin.le_last i.castSucc
  rw [min_eq_left (H.times_strictMono.monotone hi_succ_le_last),
    min_eq_left (H.times_strictMono.monotone hi_castSucc_le_last)]

/- For times at or beyond the last partition point of `H`, all truncations in
`H.brownianElementaryIntegral W t` disappear, so the stopped Itô sum has stabilized at its
terminal value. -/
theorem brownianElementaryIntegral_eq_atInfinity
    (H : PredictableStepRepresentation ℱ) (W : Process)
    {t : NNReal} (ht : H.times (Fin.last H.n) ≤ t) :
    PredictableStepRepresentation.brownianElementaryIntegral H W t =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W := by
  -- Once `t` is beyond the final partition point, every truncated increment has already reached
  -- its terminal endpoint, so the stopped sum stabilizes.
  funext ω
  rw [PredictableStepRepresentation.brownianElementaryIntegral_apply,
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity_apply]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hi_succ_le_t :
      H.times i.succ ≤ t := by
    exact (H.times_strictMono.monotone (Fin.le_last i.succ)).trans ht
  have hi_castSucc_le_t :
      H.times i.castSucc ≤ t := by
    exact (H.times_strictMono.monotone (Fin.le_last i.castSucc)).trans ht
  rw [min_eq_left hi_succ_le_t, min_eq_left hi_castSucc_le_t]

end PredictableStepRepresentation

/-- For an elementary integrand `H ∈ 𝓔` and a real process `W`, the stopped Itô
integral `brownianElementaryIntegral W H t` is obtained from a finite predictable-step
representation of `H` by the usual truncated increment sum. The representation-level formula is
recorded separately by `PredictableStepRepresentation.brownianElementaryIntegral`. -/
noncomputable def brownianElementaryIntegral {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) : Process :=
  let representation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  PredictableStepRepresentation.brownianElementaryIntegral representation W

/-- The terminal Itô integral `I_∞^W(H)` from Definition 25.3 for an elementary integrand
`H ∈ 𝓔`. -/
noncomputable def brownianElementaryIntegralAtInfinity {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) : Ω → ℝ :=
  let representation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W

/-- Helper for Definition 25.3: equal represented processes define the same canonical
predictable simple process. -/
private theorem PredictableStepRepresentation.toPredictableSimpleProcess_eq_of_toProcess_eq
    {ℱ : ContinuousFiltration} {H K : PredictableStepRepresentation ℱ}
    (hHK : H.toProcess = K.toProcess) :
    H.toPredictableSimpleProcess = K.toPredictableSimpleProcess := by
  -- Proof comment: the canonical predictable simple process is just the subtype wrapper around
  -- the represented process, so equality of the underlying processes is enough.
  apply Subtype.ext
  exact hHK

/-- Helper for Definition 25.3: no element of a finite ordered set lies strictly between two
consecutive values of its increasing `orderEmbOfFin` enumeration. -/
private theorem not_mem_Ioo_between_orderEmbOfFin_consecutive
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) (i : Fin n) {x : NNReal} (hx : x ∈ B) :
    x ∉ Set.Ioo (B.orderEmbOfFin hB i.castSucc) (B.orderEmbOfFin hB i.succ) := by
  -- Proof comment: pull `x` back to its index in the increasing enumeration and compare indices.
  intro hxIoo
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change ((B.orderIsoOfFin hB) j : NNReal) = x
    have happly :
        ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨x, hx⟩) : B) = ⟨x, hx⟩ :=
      (B.orderIsoOfFin hB).apply_symm_apply ⟨x, hx⟩
    simpa [j] using congrArg Subtype.val happly
  have hij_left : i.castSucc < j := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.1)
  have hij_right : j < i.succ := by
    exact (B.orderEmbOfFin hB).lt_iff_lt.mp (by simpa [hjx] using hxIoo.2)
  have hij_left_nat : (i : ℕ) < (j : ℕ) := by
    change ((i.castSucc : Fin (n + 1)) : ℕ) < (j : ℕ)
    exact hij_left
  have hij_right_nat : (j : ℕ) < (i : ℕ) + 1 := by
    change (j : ℕ) < ((i.succ : Fin (n + 1)) : ℕ)
    exact hij_right
  omega

/-- Helper for Definition 25.3: every element of a finite ordered set is bounded above by the
last value of its increasing `orderEmbOfFin` enumeration. -/
private theorem le_orderEmbOfFin_last_of_mem
    (B : Finset NNReal) {n : ℕ} (hB : B.card = n + 1) {x : NNReal} (hx : x ∈ B) :
    x ≤ B.orderEmbOfFin hB (Fin.last n) := by
  -- Proof comment: compare the index of `x` with the last index of the increasing enumeration.
  let j : Fin (n + 1) := (B.orderIsoOfFin hB).symm ⟨x, hx⟩
  have hjx : B.orderEmbOfFin hB j = x := by
    change ((B.orderIsoOfFin hB) j : NNReal) = x
    have happly :
        ((B.orderIsoOfFin hB) ((B.orderIsoOfFin hB).symm ⟨x, hx⟩) : B) = ⟨x, hx⟩ :=
      (B.orderIsoOfFin hB).apply_symm_apply ⟨x, hx⟩
    simpa [j] using congrArg Subtype.val happly
  exact hjx ▸ (B.orderEmbOfFin hB).monotone (Fin.le_last j)

/-- Helper for Definition 25.3: endpoint indices chosen in a common refinement preserve the order
of the original partition endpoints. -/
private theorem commonRefinementEndpointIndexStrictMono
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ)
    {nRef : ℕ} (times : Fin (nRef + 1) → NNReal) (hTimesStrictMono : StrictMono times)
    (endpointIndex : Fin (data.n + 1) → Fin (nRef + 1))
    (hEndpointIndexEq : ∀ j : Fin (data.n + 1), times (endpointIndex j) = data.times j) :
    StrictMono endpointIndex := by
  -- Proof comment: compare endpoint images through the strictly increasing refined grid.
  intro j k hjk
  have htime : times (endpointIndex j) < times (endpointIndex k) := by
    simpa [hEndpointIndexEq j, hEndpointIndexEq k] using data.times_strictMono hjk
  by_contra hnot
  exact (not_lt_of_ge (hTimesStrictMono.monotone (le_of_not_gt hnot))) htime

/-- Helper for Definition 25.3: the first original endpoint still lands at the first refined
endpoint. -/
private theorem commonRefinementEndpointIndexZero
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ)
    {nRef : ℕ} (times : Fin (nRef + 1) → NNReal) (hTimesStrictMono : StrictMono times)
    (endpointIndex : Fin (data.n + 1) → Fin (nRef + 1))
    (hEndpointIndexEq : ∀ j : Fin (data.n + 1), times (endpointIndex j) = data.times j) :
    endpointIndex 0 = 0 := by
  -- Proof comment: any positive refined index would force a positive time, contradicting that
  -- both first endpoints are `0`.
  by_contra hzero
  have hpos : 0 < (endpointIndex 0 : ℕ) := by
    apply Nat.pos_of_ne_zero
    intro hval
    apply hzero
    ext
    simpa using hval
  have htime : times 0 < times (endpointIndex 0) := hTimesStrictMono hpos
  have hzero_time : times (endpointIndex 0) = 0 := by
    simpa [data.times_zero] using hEndpointIndexEq 0
  exact (not_lt_of_ge bot_le) (hzero_time ▸ htime)

/-- Helper for Definition 25.3: on a refined block sitting inside one coarse interval, the
refined coefficient equals the original coarse coefficient. -/
private theorem commonRefinementCoeff_eq_dataCoeffOnBlock
    {ℱ : ContinuousFiltration} (data : PredictableStepRepresentation ℱ)
    {nRef : ℕ} (times : Fin (nRef + 1) → NNReal) (hTimesStrictMono : StrictMono times)
    (coeff : Fin nRef → Ω → ℝ)
    (hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        data.toProcess s = coeff i)
    (endpointIndex : Fin (data.n + 1) → Fin (nRef + 1))
    (hEndpointIndexEq : ∀ j : Fin (data.n + 1), times (endpointIndex j) = data.times j)
    {i : Fin data.n} {k : Fin nRef}
    (hk_left : (endpointIndex i.castSucc : ℕ) ≤ k)
    (hk_right : (k : ℕ) < endpointIndex i.succ) :
    coeff k = data.coeff i := by
  funext ω
  have hmem_refined : times k.succ ∈ Set.Ioc (times k.castSucc) (times k.succ) := by
    exact ⟨hTimesStrictMono k.castSucc_lt_succ, le_rfl⟩
  have hmem_coarse :
      times k.succ ∈ Set.Ioc (data.times i.castSucc) (data.times i.succ) := by
    constructor
    · calc
        data.times i.castSucc = times (endpointIndex i.castSucc) := by
          symm
          exact hEndpointIndexEq i.castSucc
        _ < times k.succ := by
          exact hTimesStrictMono (Nat.lt_succ_of_le hk_left)
    · calc
        times k.succ ≤ times (endpointIndex i.succ) := by
          exact hTimesStrictMono.monotone (Nat.succ_le_of_lt hk_right)
        _ = data.times i.succ := hEndpointIndexEq i.succ
  calc
    coeff k ω = data.toProcess (times k.succ) ω := by
      simpa using (congrFun (hCoeffEq k hmem_refined).symm ω)
    _ = data.coeff i ω := data.toProcess_eq_coeff_of_mem_interval i hmem_coarse ω

/-- Definition 25.3: rewriting a predictable-step representation on a common refined
deterministic partition should not change the stopped Brownian increment sum. -/
theorem brownianElementaryIntegral_eq_commonRefinementSum
    {ℱ : ContinuousFiltration} (W : Process) (data : PredictableStepRepresentation ℱ)
    {nRef : ℕ} (times : Fin (nRef + 1) → NNReal) (hTimesStrictMono : StrictMono times)
    (coeff : Fin nRef → Ω → ℝ)
    (hCoeffEq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        data.toProcess s = coeff i)
    (hEndpointMem :
      ∀ j : Fin (data.n + 1), ∃ k : Fin (nRef + 1), times k = data.times j)
    (hLastLe : data.times (Fin.last data.n) ≤ times (Fin.last nRef)) :
    PredictableStepRepresentation.brownianElementaryIntegral data W =
      fun t ω ↦
        ∑ i : Fin nRef,
          coeff i ω *
            (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) := by
  classical
  let endpointIndex : Fin (data.n + 1) → Fin (nRef + 1) := fun j =>
    Classical.choose (hEndpointMem j)
  have hEndpointIndexEq : ∀ j : Fin (data.n + 1), times (endpointIndex j) = data.times j := by
    intro j
    exact Classical.choose_spec (hEndpointMem j)
  have hEndpointIndexStrictMono : StrictMono endpointIndex :=
    commonRefinementEndpointIndexStrictMono data times hTimesStrictMono endpointIndex hEndpointIndexEq
  have hEndpointIndexZero : endpointIndex 0 = 0 :=
    commonRefinementEndpointIndexZero data times hTimesStrictMono endpointIndex hEndpointIndexEq
  let endpointNat : ℕ → ℕ := fun j =>
    if hj : j ≤ data.n then (endpointIndex ⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nRef + 1)) else 0
  have hEndpointNat_eq :
      ∀ {j : ℕ} (hj : j ≤ data.n),
        endpointNat j = (endpointIndex ⟨j, Nat.lt_succ_of_le hj⟩ : Fin (nRef + 1)) := by
    intro j hj
    simp [endpointNat, hj]
  have hEndpointNat_le :
      ∀ {j : ℕ} (hj : j ≤ data.n), endpointNat j ≤ nRef := by
    intro j hj
    rw [hEndpointNat_eq hj]
    exact Nat.le_of_lt_succ (endpointIndex ⟨j, Nat.lt_succ_of_le hj⟩).is_lt
  have hEndpointNat_zero : endpointNat 0 = 0 := by
    change (endpointIndex ⟨0, Nat.succ_pos _⟩ : ℕ) = 0
    simpa using congrArg Fin.val hEndpointIndexZero
  have hEndpointNat_last :
      endpointNat data.n = (endpointIndex (Fin.last data.n) : Fin (nRef + 1)) := by
    rw [hEndpointNat_eq le_rfl]
    rfl
  have hEndpointNat_succ_mono :
      ∀ {j : ℕ} (hj : j < data.n), endpointNat j ≤ endpointNat (j + 1) := by
    intro j hj
    rw [hEndpointNat_eq (Nat.le_of_lt hj), hEndpointNat_eq (Nat.succ_le_of_lt hj)]
    exact (hEndpointIndexStrictMono (by simpa using Nat.lt_succ_self j)).le
  have hEndpointNat_castSucc :
      ∀ i : Fin data.n, endpointNat i = (endpointIndex i.castSucc : ℕ) := by
    intro i
    rw [hEndpointNat_eq (Nat.le_of_lt i.is_lt)]
    rfl
  have hEndpointNat_succ :
      ∀ i : Fin data.n, endpointNat (i + 1) = (endpointIndex i.succ : ℕ) := by
    intro i
    rw [hEndpointNat_eq (Nat.succ_le_of_lt i.is_lt)]
    rfl
  have hCoeffOnBlock :
      ∀ i : Fin data.n, ∀ k : Fin nRef,
        (endpointIndex i.castSucc : ℕ) ≤ k →
        (k : ℕ) < endpointIndex i.succ →
        coeff k = data.coeff i := by
    intro i k hk_left hk_right
    exact commonRefinementCoeff_eq_dataCoeffOnBlock data times hTimesStrictMono coeff hCoeffEq
      endpointIndex hEndpointIndexEq hk_left hk_right
  have hTailCoeffZero :
      ∀ k : Fin nRef, endpointNat data.n ≤ (k : ℕ) → coeff k = 0 := by
    intro k hk
    funext ω
    have hlast_lt :
        data.times (Fin.last data.n) < times k.succ := by
      have hk' : (endpointIndex (Fin.last data.n) : ℕ) ≤ (k : ℕ) := by
        simpa [hEndpointNat_last] using hk
      calc
        data.times (Fin.last data.n) = times (endpointIndex (Fin.last data.n)) := by
          symm
          exact hEndpointIndexEq (Fin.last data.n)
        _ < times k.succ := by
          exact hTimesStrictMono (Nat.lt_succ_of_le hk')
    have hmem : times k.succ ∈ Set.Ioc (times k.castSucc) (times k.succ) := by
      exact ⟨hTimesStrictMono k.castSucc_lt_succ, le_rfl⟩
    calc
      coeff k ω = data.toProcess (times k.succ) ω := by
        simpa using (congrFun (hCoeffEq k hmem).symm ω)
      _ = 0 := data.toProcess_eq_zero_of_last_lt hlast_lt ω
  -- Route correction: the old coarse-endpoint prefix invariant kept reopening the same nat/Fin
  -- coercions. We instead convert once to nat-indexed refined summands, telescope each coarse
  -- block, cover the refined prefix by those blocks, and kill the remaining tail by zero
  -- coefficients.
  funext t ω
  let x : ℕ → ℝ := fun j =>
    if hj : j ≤ nRef then W (min (times ⟨j, Nat.lt_succ_of_le hj⟩) t) ω else 0
  let s : ℕ → ℝ := fun k =>
    if hk : k < nRef then coeff ⟨k, hk⟩ ω * (x (k + 1) - x k) else 0
  -- Proof comment: consecutive coarse endpoints stay strictly ordered after passing to the
  -- common-refinement indices, so the refined strips split into genuine nonempty `Ico` blocks.
  have hEndpointNat_strictSucc :
      ∀ {j : ℕ} (hj : j < data.n), endpointNat j < endpointNat (j + 1) := by
    intro j hj
    rw [hEndpointNat_eq (Nat.le_of_lt hj), hEndpointNat_eq (Nat.succ_le_of_lt hj)]
    exact hEndpointIndexStrictMono (by simpa using Nat.lt_succ_self j)
  -- Proof comment: `x` is just the Brownian path evaluated on the refined partition whenever the
  -- nat index stays inside the refinement range.
  have hX_apply :
      ∀ {j : ℕ} (hj : j ≤ nRef),
        x j = W (min (times ⟨j, Nat.lt_succ_of_le hj⟩) t) ω := by
    intro j hj
    simp [x, hj]
  -- Proof comment: `s` is the nat-indexed refined Brownian summand on valid refined strips.
  have hSummand_apply :
      ∀ {k : ℕ} (hk : k < nRef),
        s k = coeff ⟨k, hk⟩ ω * (x (k + 1) - x k) := by
    intro k hk
    simp [s, hk]
  -- Proof comment: at coarse endpoints, the nat-indexed path values recover the original coarse
  -- Brownian truncations exactly.
  have hX_endpoint_castSucc :
      ∀ i : Fin data.n,
        x (endpointNat i) = W (min (data.times i.castSucc) t) ω := by
    intro i
    have hi_le : endpointNat i ≤ nRef := hEndpointNat_le (Nat.le_of_lt i.is_lt)
    have hcast :
        (⟨endpointNat i, Nat.lt_succ_of_le hi_le⟩ : Fin (nRef + 1)) = endpointIndex i.castSucc := by
      ext
      simp [hEndpointNat_castSucc i]
    rw [hX_apply hi_le, hcast, hEndpointIndexEq i.castSucc]
  have hX_endpoint_succ :
      ∀ i : Fin data.n,
        x (endpointNat (i + 1)) = W (min (data.times i.succ) t) ω := by
    intro i
    have hi_le : endpointNat (i + 1) ≤ nRef := hEndpointNat_le (Nat.succ_le_of_lt i.is_lt)
    have hcast :
        (⟨endpointNat (i + 1), Nat.lt_succ_of_le hi_le⟩ : Fin (nRef + 1)) = endpointIndex i.succ := by
      ext
      simp [hEndpointNat_succ i]
    rw [hX_apply hi_le, hcast, hEndpointIndexEq i.succ]
  -- Proof comment: converting the refined `Fin` sum to a nat-indexed range sum lets every later
  -- step stay in the same `Ico` normal form.
  have hRefinedSum_nat :
      (∑ i : Fin nRef,
        coeff i ω * (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω)) =
      ∑ k ∈ Finset.range nRef, s k := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hklt : k < nRef := Finset.mem_range.mp hk
    have hk_le : k ≤ nRef := Nat.le_of_lt hklt
    have hk1_le : k + 1 ≤ nRef := Nat.succ_le_of_lt hklt
    have hcast :
        (⟨k, Nat.lt_succ_of_le hk_le⟩ : Fin (nRef + 1)) = (⟨k, hklt⟩ : Fin nRef).castSucc := by
      ext
      rfl
    have hsucc :
        (⟨k + 1, Nat.lt_succ_of_le hk1_le⟩ : Fin (nRef + 1)) = (⟨k, hklt⟩ : Fin nRef).succ := by
      ext
      rfl
    have hxCast :
        x k = W (min (times (⟨k, hklt⟩ : Fin nRef).castSucc) t) ω := by
      rw [hX_apply hk_le, hcast]
    have hxSucc :
        x (k + 1) = W (min (times (⟨k, hklt⟩ : Fin nRef).succ) t) ω := by
      rw [hX_apply hk1_le, hsucc]
    symm
    simpa [s, hklt, hxSucc, hxCast]
  -- Proof comment: on each coarse block, all refined coefficients agree with the coarse one, so
  -- the block sum telescopes to the single coarse Brownian increment.
  have hBlockSum :
      ∀ i : Fin data.n,
        ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)), s k =
          data.coeff i ω *
            (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω) := by
    intro i
    have hi_right_le : endpointNat (i + 1) ≤ nRef := hEndpointNat_le (Nat.succ_le_of_lt i.is_lt)
    have hi_strict : endpointNat i < endpointNat (i + 1) := hEndpointNat_strictSucc i.is_lt
    calc
      ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)), s k =
          ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)),
            data.coeff i ω * (x (k + 1) - x k) := by
              refine Finset.sum_congr rfl fun k hk ↦ ?_
              have hk_mem := Finset.mem_Ico.mp hk
              have hklt : k < nRef := lt_of_lt_of_le hk_mem.2 hi_right_le
              have hk_left : (endpointIndex i.castSucc : ℕ) ≤ k := by
                simpa [hEndpointNat_castSucc i] using hk_mem.1
              have hk_right : (k : ℕ) < endpointIndex i.succ := by
                simpa [hEndpointNat_succ i] using hk_mem.2
              rw [hSummand_apply hklt, hCoeffOnBlock i ⟨k, hklt⟩ hk_left hk_right]
      _ =
          data.coeff i ω *
            ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)), (x (k + 1) - x k) := by
              rw [← Finset.mul_sum]
      _ = data.coeff i ω * (x (endpointNat (i + 1)) - x (endpointNat i)) := by
            have hTel :
                ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)), (x (k + 1) - x k) =
                  x (endpointNat (i + 1)) - x (endpointNat i) := by
              rw [Finset.sum_sub_distrib,
                Finset.sum_Ico_add' x (endpointNat i) (endpointNat (i + 1)) 1,
                Finset.sum_Ico_eq_sub x (Nat.succ_le_succ hi_strict.le),
                Finset.sum_Ico_eq_sub x hi_strict.le,
                Finset.sum_range_succ, Finset.sum_range_succ]
              ring
            rw [hTel]
      _ =
          data.coeff i ω *
            (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω) := by
              rw [hX_endpoint_succ i, hX_endpoint_castSucc i]
  -- Proof comment: the consecutive coarse blocks concatenate to the whole refined prefix up to
  -- the last coarse endpoint.
  have hBlocks_cover_prefix :
      ∀ m ≤ data.n,
        (∑ i ∈ Finset.range m,
          ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)), s k) =
        ∑ k ∈ Finset.range (endpointNat m), s k := by
    intro m hm
    induction' m with m hm_ind
    · simp [hEndpointNat_zero]
    · have hm_le : m ≤ data.n := Nat.le_of_succ_le hm
      have hm_lt : m < data.n := Nat.lt_of_succ_le hm
      rw [Finset.sum_range_succ, hm_ind hm_le]
      simpa using Finset.sum_range_add_sum_Ico s (hEndpointNat_strictSucc hm_lt).le
  -- Proof comment: every refined strip after the last coarse endpoint has zero coefficient, so
  -- the tail contribution past `endpointNat data.n` vanishes.
  have hTailSum_eq_zero :
      ∑ k ∈ Finset.Ico (endpointNat data.n) nRef, s k = 0 := by
    refine Finset.sum_eq_zero fun k hk ↦ ?_
    have hk_mem := Finset.mem_Ico.mp hk
    have hklt : k < nRef := hk_mem.2
    rw [hSummand_apply hklt, hTailCoeffZero ⟨k, hklt⟩ hk_mem.1]
    simp
  -- Proof comment: splitting the refined range at the last coarse endpoint reduces the final
  -- assembly to the prefix covered by coarse blocks.
  have hRefinedPrefix :
      ∑ k ∈ Finset.range nRef, s k = ∑ k ∈ Finset.range (endpointNat data.n), s k := by
    have hsplit :
        (∑ k ∈ Finset.range (endpointNat data.n), s k) +
            ∑ k ∈ Finset.Ico (endpointNat data.n) nRef, s k =
          ∑ k ∈ Finset.range nRef, s k := by
      simpa using Finset.sum_range_add_sum_Ico s (hEndpointNat_le le_rfl)
    rw [hTailSum_eq_zero, add_zero] at hsplit
    exact hsplit.symm
  calc
    PredictableStepRepresentation.brownianElementaryIntegral data W t ω =
        ∑ i : Fin data.n,
          data.coeff i ω *
            (W (min (data.times i.succ) t) ω - W (min (data.times i.castSucc) t) ω) := by
              rw [PredictableStepRepresentation.brownianElementaryIntegral_apply]
    _ =
        ∑ i ∈ Finset.range data.n,
          ∑ k ∈ Finset.Ico (endpointNat i) (endpointNat (i + 1)), s k := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl fun j hj ↦ ?_
            let i : Fin data.n := ⟨j, Finset.mem_range.mp hj⟩
            have hjlt : j < data.n := Finset.mem_range.mp hj
            simpa [i, hjlt] using (hBlockSum i).symm
    _ = ∑ k ∈ Finset.range (endpointNat data.n), s k := by
          simpa using hBlocks_cover_prefix data.n le_rfl
    _ = ∑ k ∈ Finset.range nRef, s k := hRefinedPrefix.symm
    _ =
        ∑ i : Fin nRef,
          coeff i ω * (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) := by
            exact hRefinedSum_nat.symm

/-- The stopped Brownian increment sum depends only on the underlying predictable simple process,
not on the chosen predictable-step representation. -/
theorem brownianElementaryIntegral_congr {ℱ : ContinuousFiltration}
    (W : Process) {H K : PredictableStepRepresentation ℱ} (hHK : H.toProcess = K.toProcess) :
    PredictableStepRepresentation.brownianElementaryIntegral H W =
      PredictableStepRepresentation.brownianElementaryIntegral K W := by
  classical
  -- Route correction: compare both representations through one common refinement of their
  -- boundary sets, then reduce the remaining work to one telescoping refinement lemma.
  let B : Finset NNReal := Finset.image H.times Finset.univ ∪ Finset.image K.times Finset.univ
  have hB0 : (0 : NNReal) ∈ B := by
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨0, Finset.mem_univ _, H.times_zero⟩
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨0, hB0⟩
  let nRef : ℕ := B.card - 1
  have hBcard : B.card = nRef + 1 := by
    have hcard : B.card = (B.card - 1) + 1 := by
      omega
    simpa [nRef] using hcard
  let times : Fin (nRef + 1) → NNReal := B.orderEmbOfFin hBcard
  have hTimesStrictMono : StrictMono times := (B.orderEmbOfFin hBcard).strictMono
  have hStripH :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) → H.toProcess s = g := by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin H.n, H.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive (B := B) (hB := hBcard) (i := i)
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩
    -- Proof comment: each refined strip contains no old `H`-boundary, so `H` is constant there.
    exact H.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  have hStripK :
      ∀ i : Fin nRef,
        ∃ g : Ω → ℝ,
          Measurable[ℱ (times i.castSucc)] g ∧
          (∃ C : ℝ, ∀ ω, |g ω| ≤ C) ∧
          ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) → K.toProcess s = g := by
    intro i
    have huv : times i.castSucc < times i.succ := hTimesStrictMono i.castSucc_lt_succ
    have hboundary :
        ∀ j : Fin K.n, K.times j.succ ∉ Set.Ioo (times i.castSucc) (times i.succ) := by
      intro j
      apply not_mem_Ioo_between_orderEmbOfFin_consecutive (B := B) (hB := hBcard) (i := i)
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨j.succ, Finset.mem_univ _, rfl⟩
    -- Proof comment: the same common-refinement argument applies to `K`.
    exact K.exists_bddMeasurable_eq_on_Ioc_of_no_boundary huv hboundary
  let coeffH : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStripH i)
  let coeffK : Fin nRef → Ω → ℝ := fun i ↦ Classical.choose (hStripK i)
  have hCoeffH_eq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        H.toProcess s = coeffH i := by
    intro i s hs
    exact (Classical.choose_spec (hStripH i)).2.2 hs
  have hCoeffK_eq :
      ∀ i : Fin nRef, ∀ ⦃s : NNReal⦄, s ∈ Set.Ioc (times i.castSucc) (times i.succ) →
        K.toProcess s = coeffK i := by
    intro i s hs
    exact (Classical.choose_spec (hStripK i)).2.2 hs
  have hCoeffEq : ∀ i : Fin nRef, coeffH i = coeffK i := by
    intro i
    funext ω
    have hi_mem : times i.succ ∈ Set.Ioc (times i.castSucc) (times i.succ) := by
      exact ⟨hTimesStrictMono i.castSucc_lt_succ, le_rfl⟩
    have hH_eval : H.toProcess (times i.succ) ω = coeffH i ω := by
      exact congrFun (hCoeffH_eq i hi_mem) ω
    have hK_eval : K.toProcess (times i.succ) ω = coeffK i ω := by
      exact congrFun (hCoeffK_eq i hi_mem) ω
    calc
      coeffH i ω = H.toProcess (times i.succ) ω := by simpa using hH_eval.symm
      _ = K.toProcess (times i.succ) ω := by
            simpa using congrArg (fun f : Process => f (times i.succ) ω) hHK
      _ = coeffK i ω := hK_eval
  have hEndpointMemH :
      ∀ j : Fin (H.n + 1), ∃ k : Fin (nRef + 1), times k = H.times j := by
    intro j
    have hj : H.times j ∈ B := by
      apply Finset.mem_union_left
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    refine ⟨(B.orderIsoOfFin hBcard).symm ⟨H.times j, hj⟩, ?_⟩
    change ((B.orderIsoOfFin hBcard) ((B.orderIsoOfFin hBcard).symm ⟨H.times j, hj⟩) :
      NNReal) = H.times j
    simpa using congrArg Subtype.val
      ((B.orderIsoOfFin hBcard).apply_symm_apply ⟨H.times j, hj⟩)
  have hEndpointMemK :
      ∀ j : Fin (K.n + 1), ∃ k : Fin (nRef + 1), times k = K.times j := by
    intro j
    have hj : K.times j ∈ B := by
      apply Finset.mem_union_right
      exact Finset.mem_image.2 ⟨j, Finset.mem_univ _, rfl⟩
    refine ⟨(B.orderIsoOfFin hBcard).symm ⟨K.times j, hj⟩, ?_⟩
    change ((B.orderIsoOfFin hBcard) ((B.orderIsoOfFin hBcard).symm ⟨K.times j, hj⟩) :
      NNReal) = K.times j
    simpa using congrArg Subtype.val
      ((B.orderIsoOfFin hBcard).apply_symm_apply ⟨K.times j, hj⟩)
  have hLastH_le : H.times (Fin.last H.n) ≤ times (Fin.last nRef) := by
    apply le_orderEmbOfFin_last_of_mem (B := B) (hB := hBcard)
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨Fin.last H.n, Finset.mem_univ _, rfl⟩
  have hLastK_le : K.times (Fin.last K.n) ≤ times (Fin.last nRef) := by
    apply le_orderEmbOfFin_last_of_mem (B := B) (hB := hBcard)
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨Fin.last K.n, Finset.mem_univ _, rfl⟩
  have hIntegralH :
      PredictableStepRepresentation.brownianElementaryIntegral H W =
        fun t ω ↦
          ∑ i : Fin nRef,
            coeffH i ω *
              (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) :=
    brownianElementaryIntegral_eq_commonRefinementSum (W := W) H times hTimesStrictMono coeffH
      hCoeffH_eq hEndpointMemH hLastH_le
  have hIntegralK :
      PredictableStepRepresentation.brownianElementaryIntegral K W =
        fun t ω ↦
          ∑ i : Fin nRef,
            coeffK i ω *
              (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) :=
    brownianElementaryIntegral_eq_commonRefinementSum (W := W) K times hTimesStrictMono coeffK
      hCoeffK_eq hEndpointMemK hLastK_le
  have hCommonSum :
      (fun t ω ↦
        ∑ i : Fin nRef,
          coeffH i ω *
            (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω)) =
      fun t ω ↦
        ∑ i : Fin nRef,
          coeffK i ω *
            (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) := by
    -- Proof comment: the common refinement coefficients agree stripwise because `H.toProcess`
    -- and `K.toProcess` agree at every refined right endpoint.
    funext t ω
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hCoeffEq i]
  calc
    PredictableStepRepresentation.brownianElementaryIntegral H W =
        fun t ω ↦
          ∑ i : Fin nRef,
            coeffH i ω *
              (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) := hIntegralH
    _ =
        fun t ω ↦
          ∑ i : Fin nRef,
            coeffK i ω *
              (W (min (times i.succ) t) ω - W (min (times i.castSucc) t) ω) := hCommonSum
    _ = PredictableStepRepresentation.brownianElementaryIntegral K W := hIntegralK.symm

/-- The terminal Brownian increment sum depends only on the underlying predictable simple process,
not on the chosen predictable-step representation. -/
theorem brownianElementaryIntegralAtInfinity_congr {ℱ : ContinuousFiltration}
    (W : Process) {H K : PredictableStepRepresentation ℱ} (hHK : H.toProcess = K.toProcess) :
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity K W := by
  -- Proof comment: evaluate the stopped congruence at a time beyond both terminal partition
  -- points, where each stopped increment sum has already stabilized to its terminal value.
  let t : NNReal := max (H.times (Fin.last H.n)) (K.times (Fin.last K.n))
  have hHt : H.times (Fin.last H.n) ≤ t := le_max_left _ _
  have hKt : K.times (Fin.last K.n) ≤ t := le_max_right _ _
  have hStopped :
      PredictableStepRepresentation.brownianElementaryIntegral H W t =
        PredictableStepRepresentation.brownianElementaryIntegral K W t :=
    congrFun (brownianElementaryIntegral_congr (W := W) hHK) t
  calc
    PredictableStepRepresentation.brownianElementaryIntegralAtInfinity H W =
        PredictableStepRepresentation.brownianElementaryIntegral H W t := by
          symm
          exact PredictableStepRepresentation.brownianElementaryIntegral_eq_atInfinity H W hHt
    _ = PredictableStepRepresentation.brownianElementaryIntegral K W t := hStopped
    _ = PredictableStepRepresentation.brownianElementaryIntegralAtInfinity K W := by
          exact PredictableStepRepresentation.brownianElementaryIntegral_eq_atInfinity K W hKt

/-- Any predictable-step representation of `H` computes the stopped Brownian integral from
Definition 25.3. -/
theorem brownianElementaryIntegral_spec {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) {representation : PredictableStepRepresentation ℱ}
    (hrepresentation : (H : Process) = representation.toProcess) :
    brownianElementaryIntegral W H =
      PredictableStepRepresentation.brownianElementaryIntegral representation W := by
  -- Compare the chosen representation of `H` to the supplied one through the common underlying
  -- process `(H : Process)`.
  let chosenRepresentation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  have hchosen :
      (H : Process) = chosenRepresentation.toProcess :=
    Classical.choose_spec (PredictableSimpleProcess.exists_representation H)
  rw [brownianElementaryIntegral]
  exact brownianElementaryIntegral_congr (W := W)
    (hchosen.symm.trans hrepresentation)

/-- Any predictable-step representation of `H` computes the terminal Brownian integral from
Definition 25.3. -/
theorem brownianElementaryIntegralAtInfinity_spec {ℱ : ContinuousFiltration} (W : Process)
    (H : PredictableSimpleProcess ℱ) {representation : PredictableStepRepresentation ℱ}
    (hrepresentation : (H : Process) = representation.toProcess) :
    brownianElementaryIntegralAtInfinity W H =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W := by
  -- Compare the chosen representation of `H` to the supplied one through the common underlying
  -- process `(H : Process)`.
  let chosenRepresentation : PredictableStepRepresentation ℱ :=
    Classical.choose (PredictableSimpleProcess.exists_representation H)
  have hchosen :
      (H : Process) = chosenRepresentation.toProcess :=
    Classical.choose_spec (PredictableSimpleProcess.exists_representation H)
  rw [brownianElementaryIntegralAtInfinity]
  exact brownianElementaryIntegralAtInfinity_congr (W := W)
    (hchosen.symm.trans hrepresentation)

/-- On the canonical predictable simple process attached to a predictable-step representation,
Definition 25.3 recovers the representation-level stopped increment sum. -/
@[simp] theorem brownianElementaryIntegral_toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (W : Process) (representation : PredictableStepRepresentation ℱ) :
    brownianElementaryIntegral W representation.toPredictableSimpleProcess =
      PredictableStepRepresentation.brownianElementaryIntegral representation W :=
  brownianElementaryIntegral_spec W representation.toPredictableSimpleProcess
    representation.toPredictableSimpleProcess_coe

/-- On the canonical predictable simple process attached to a predictable-step representation,
Definition 25.3 recovers the representation-level terminal increment sum. -/
@[simp] theorem brownianElementaryIntegralAtInfinity_toPredictableSimpleProcess
    {ℱ : ContinuousFiltration} (W : Process) (representation : PredictableStepRepresentation ℱ) :
    brownianElementaryIntegralAtInfinity W representation.toPredictableSimpleProcess =
      PredictableStepRepresentation.brownianElementaryIntegralAtInfinity representation W :=
  brownianElementaryIntegralAtInfinity_spec W representation.toPredictableSimpleProcess
    representation.toPredictableSimpleProcess_coe

end MeasureTheory

end

/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped BigOperators
open Preorder Finset

noncomputable section

universe u

section

variable {d n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- The kernel family driving the random walk with increment laws `μ`, viewed as a family on
finite prefix trajectories. -/
private def convolutionTrajectoryKernel (μ : Fin n → ProbabilityMeasure E) :
    (k : ℕ) → Kernel ((i : Finset.Iic k) → E) E
  | k =>
      if hk : k < n then
        let current : Finset.Iic k := ⟨k, Finset.mem_Iic.2 le_rfl⟩
        (dirac_convolution_kernel (μ ⟨k, hk⟩ : Measure E)).comap
          (fun x : (i : Finset.Iic k) → E ↦ x current)
          (measurable_pi_apply current)
      else
        Kernel.const ((i : Finset.Iic k) → E) (Measure.dirac (0 : E))

/-- Helper for Theorem 14.28: the cumulative-sum map sending an increment vector
`(x₁, …, xₙ)` to the partial-sum path `(x₁, x₁ + x₂, …, x₁ + ⋯ + xₙ)`. -/
private def partialSumPath (z : Fin n → E) : (i : Finset.Ioc 0 n) → E :=
  fun i ↦
    Fin.partialSum z ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 i.2).2⟩

/-- Helper for Theorem 14.28: each finite partial-sum coordinate is a measurable function of the
increment vector. -/
private theorem measurable_finPartialSum (m : Fin (n + 1)) :
    Measurable (fun z : Fin n → E ↦ Fin.partialSum z m) := by
  induction m using Fin.induction with
  | zero =>
      -- Proof comment: the zeroth partial sum is constantly `0`.
      simp
  | succ i hi =>
      -- Proof comment: a successor partial sum is the previous one plus the next coordinate.
      simpa [Fin.partialSum_succ] using hi.add (measurable_pi_apply i)

/-- Helper for Theorem 14.28: the cumulative-sum map on increment vectors is measurable. -/
private theorem measurable_partialSumPath :
    Measurable (partialSumPath (d := d) (n := n)) := by
  -- Proof comment: measurability is checked coordinatewise, using the finite partial-sum
  -- measurability lemma on each output coordinate.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [partialSumPath] using
    measurable_finPartialSum (d := d) (n := n)
      ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 i.2).2⟩

/-- Helper for Theorem 14.28: the source-facing index set `Fin n` is canonically equivalent to
`Finset.Ioc 0 n`. -/
private def finIocEquiv : Fin n ≃ Finset.Ioc 0 n where
  toFun i := ⟨i.1 + 1, Finset.mem_Ioc.2 ⟨Nat.succ_pos _, Nat.succ_le_of_lt i.2⟩⟩
  invFun i :=
    ⟨i.1 - 1, by
      have hi0 : 0 < i.1 := (Finset.mem_Ioc.1 i.2).1
      have hin : i.1 ≤ n := (Finset.mem_Ioc.1 i.2).2
      exact lt_of_lt_of_le
        (Nat.sub_lt (Nat.succ_le_of_lt hi0) (Nat.succ_pos 0))
        hin⟩
  left_inv i := by
    -- Proof comment: reindexing from `Fin n` to `Ioc 0 n` and back preserves the underlying
    -- natural number.
    apply Fin.ext
    simp
  right_inv i := by
    -- Proof comment: every element of `Ioc 0 n` is of the form `j + 1`, so the inverse sends it
    -- back to `j`.
    apply Subtype.ext
    have hi0 : 0 < i.1 := (Finset.mem_Ioc.1 i.2).1
    have h1 : 1 ≤ i.1 := Nat.succ_le_of_lt hi0
    simp [Nat.sub_add_cancel h1]

/-- Helper for Theorem 14.28: transporting the `Ioc 0 n`-indexed product increment law along the
explicit equivalence `Finset.Ioc 0 n ≃ Fin n` recovers the usual `Fin n`-indexed product law. -/
private theorem iocIncrementProduct_eq_finIncrementProduct
    (μ : Fin n → ProbabilityMeasure E) :
    (Measure.pi fun i : Finset.Ioc 0 n ↦ (μ ((finIocEquiv (n := n)).symm i) : Measure E)).map
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ E) (finIocEquiv (n := n)).symm)
      = Measure.pi fun i : Fin n ↦ (μ i : Measure E) := by
  -- Proof comment: this is the standard product-measure reindexing theorem applied to the
  -- concrete equivalence between `Fin n` and `Ioc 0 n`.
  simpa using
    (Measure.pi_map_piCongrLeft
      (e := (finIocEquiv (n := n)).symm)
      (β := fun _ : Fin n ↦ E)
      (μ := fun i : Fin n ↦ (μ i : Measure E)))

/-- Helper for Theorem 14.28: each convolution step kernel is the pushforward of the next
increment law by translation by the current position. -/
private theorem convolutionStep_apply_eq_map_add
    (μ : Fin n → ProbabilityMeasure E) {k : ℕ} (hk : k < n)
    (x : (i : Finset.Iic k) → E) :
    convolutionTrajectoryKernel μ k x =
      Measure.map (fun z : E ↦ x ⟨k, Finset.mem_Iic.2 le_rfl⟩ + z) (μ ⟨k, hk⟩ : Measure E) := by
  -- Proof comment: unfold the owner kernel at a valid time `k`; it is the translated increment
  -- law `δ_{x_k} * μ_k`, which is exactly the pushforward by addition.
  rw [convolutionTrajectoryKernel, dif_pos hk]
  simp only [Kernel.comap_apply, dirac_convolution_kernel_apply]
  simpa using
    (Measure.dirac_conv (x ⟨k, Finset.mem_Iic.2 le_rfl⟩) (μ ⟨k, hk⟩ : Measure E))

/-- Helper for Theorem 14.28: forgetting the time-`0` coordinate turns a full `Iic n` increment
history into the `Fin n`-indexed increment vector used by `partialSumPath`. -/
private def tailIncrementVector (z : (i : Finset.Iic n) → E) : Fin n → E :=
  fun j ↦ z ⟨((finIocEquiv (n := n)) j).1, Ioc_subset_Iic_self ((finIocEquiv (n := n)) j).2⟩

/-- Helper for Theorem 14.28: the tail-increment extraction map is measurable. -/
private theorem measurable_tailIncrementVector :
    Measurable (tailIncrementVector (d := d) (n := n)) := by
  -- Proof comment: each coordinate is just evaluation at one fixed nonzero time index.
  refine measurable_pi_lambda _ fun j ↦ ?_
  let ij : Finset.Iic n :=
    ⟨((finIocEquiv (n := n)) j).1, Ioc_subset_Iic_self ((finIocEquiv (n := n)) j).2⟩
  have hij : Measurable (fun z : (i : Finset.Iic n) → E ↦ z ij) := measurable_pi_apply ij
  simpa [tailIncrementVector, ij] using hij

/-- Helper for Theorem 14.28: a full increment history on `Iic n` determines the full path
history on the same index set, with time `0` fixed at `0` and later coordinates given by
partial sums of the nonzero increments. -/
private def fullPartialSumHistory (z : (i : Finset.Iic n) → E) : (i : Finset.Iic n) → E :=
  fun i ↦
    if h0 : i.1 = 0 then
      0
    else
      partialSumPath (d := d) (n := n) (tailIncrementVector (d := d) (n := n) z)
        ⟨i.1, Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero h0, Finset.mem_Iic.1 i.2⟩⟩

/-- Helper for Theorem 14.28: the full-history cumulative-sum map is measurable. -/
private theorem measurable_fullPartialSumHistory :
    Measurable (fullPartialSumHistory (d := d) (n := n)) := by
  -- Proof comment: every output coordinate is either constantly `0` or one coordinate of the
  -- measurable `partialSumPath` composed with the measurable tail projection.
  refine measurable_pi_lambda _ fun i ↦ ?_
  by_cases h0 : i.1 = 0
  · simp [fullPartialSumHistory, h0]
  · let ii : Finset.Ioc 0 n :=
      ⟨i.1, Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero h0, Finset.mem_Iic.1 i.2⟩⟩
    have happly : Measurable (fun w : (j : Finset.Ioc 0 n) → E ↦ w ii) :=
      measurable_pi_apply ii
    have hcoord :
        Measurable (fun z : (j : Finset.Iic n) → E ↦
          partialSumPath (d := d) (n := n)
            (tailIncrementVector (d := d) (n := n) z) ii) :=
      happly.comp
        ((measurable_partialSumPath (d := d) (n := n)).comp
          (measurable_tailIncrementVector (d := d) (n := n)))
    simpa [fullPartialSumHistory, h0, ii] using hcoord

/-- Helper for Theorem 14.28: restrict a full history on `Iic n` to its nonzero coordinates. -/
private def restrictNonzeroHistory (z : (i : Finset.Iic n) → E) : (i : Finset.Ioc 0 n) → E :=
  Finset.restrict₂ (π := fun _ : ℕ ↦ E) Ioc_subset_Iic_self z

/-- Helper for Theorem 14.28: the nonzero-coordinate restriction map is measurable. -/
private theorem measurable_restrictNonzeroHistory :
    Measurable (restrictNonzeroHistory (d := d) (n := n)) := by
  -- Proof comment: this is exactly the standard measurable restriction map on dependent product
  -- histories.
  simpa [restrictNonzeroHistory] using
    (Finset.measurable_restrict₂ (X := fun _ : ℕ ↦ E) Ioc_subset_Iic_self)

/-- Helper for Theorem 14.28: gluing one fresh increment onto an old increment history and then
taking cumulative sums agrees with first taking cumulative sums and then translating only the
terminal coordinate by the fresh increment. -/
private theorem fullPartialSumHistory_IicProdIoc
    (x : (i : Finset.Iic n) → E) (u : E) :
    fullPartialSumHistory (d := d) (n := n + 1)
      (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1)
        (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n u)) =
      _root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1)
        (fullPartialSumHistory (d := d) (n := n) x,
          MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n
            ((fullPartialSumHistory (d := d) (n := n) x)
              ⟨n, Finset.mem_Iic.2 le_rfl⟩ + u)) := by
  -- Proof comment: on the old coordinates both sides read the same prefix partial sums; on the
  -- new coordinate the final partial sum is the previous endpoint plus the fresh increment.
  let tail' : Fin (n + 1) → E :=
    tailIncrementVector (d := d) (n := n + 1)
      (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) n (n + 1)
        (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) n u))
  have htail : Fin.init tail' = tailIncrementVector (d := d) (n := n) x := by
    ext j
    simp [tail', Fin.init, tailIncrementVector, _root_.IicProdIoc_def, finIocEquiv,
      MeasurableEquiv.piSingleton]
  have hlast : tail' (Fin.last n) = u := by
    simp [tail', tailIncrementVector, _root_.IicProdIoc_def, finIocEquiv,
      MeasurableEquiv.piSingleton]
  ext i coord
  by_cases hi : i.1 ≤ n
  · by_cases h0 : i.1 = 0
    · have hi0 : i = ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩ := by
        apply Subtype.ext
        simpa using h0
      subst hi0
      simp [fullPartialSumHistory, _root_.IicProdIoc_def]
    · let ii : Finset.Ioc 0 n := ⟨i.1, Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero h0, hi⟩⟩
      let ii' : Finset.Ioc 0 (n + 1) :=
        ⟨i.1, Finset.mem_Ioc.2 ⟨Nat.pos_of_ne_zero h0, le_trans hi (Nat.le_succ n)⟩⟩
      let m : Fin (n + 1) := ⟨i.1, Nat.lt_succ_of_le hi⟩
      have hm :
          m.castSucc = ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 ii'.2).2⟩ := by
        apply Fin.ext
        rfl
      have hprefix :
          partialSumPath (d := d) (n := n + 1) tail' ii' =
            partialSumPath (d := d) (n := n) (tailIncrementVector (d := d) (n := n) x) ii := by
        rw [show
            partialSumPath (d := d) (n := n + 1) tail' ii' =
              Fin.partialSum tail' m.castSucc by
              rw [partialSumPath, hm]]
        rw [show
            partialSumPath (d := d) (n := n) (tailIncrementVector (d := d) (n := n) x) ii =
              Fin.partialSum (tailIncrementVector (d := d) (n := n) x) m by
              rw [partialSumPath]]
        rw [← Fin.partialSum_init (f := tail') m, htail]
      simpa [tail', ii, ii', fullPartialSumHistory, _root_.IicProdIoc_def, hi, h0] using
        congrArg (fun v : E ↦ v coord) hprefix
  · have hi_eq : i.1 = n + 1 := by
      have hge : n + 1 ≤ i.1 := Nat.succ_le_of_lt (lt_of_not_ge hi)
      exact le_antisymm (Finset.mem_Iic.1 i.2) hge
    have hi_last : i = ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ := by
      apply Subtype.ext
      simpa using hi_eq
    subst hi_last
    have hlastIndex : (⟨n + 1, Nat.lt_succ_self (n + 1)⟩ : Fin (n + 2)) = (Fin.last n).succ := by
      apply Fin.ext
      simp
    have hprevIndex : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp
    have hlastPath :
        partialSumPath (d := d) (n := n + 1) tail'
          ⟨n + 1, Finset.mem_Ioc.2 ⟨Nat.succ_pos n, le_rfl⟩⟩ =
          (fullPartialSumHistory (d := d) (n := n) x) ⟨n, Finset.mem_Iic.2 le_rfl⟩ + u := by
      rw [show
          partialSumPath (d := d) (n := n + 1) tail'
            ⟨n + 1, Finset.mem_Ioc.2 ⟨Nat.succ_pos n, le_rfl⟩⟩ =
            Fin.partialSum tail' (Fin.last n).succ by
            rw [partialSumPath, hlastIndex]]
      rw [Fin.partialSum_succ, ← Fin.partialSum_init (f := tail') (Fin.last n), htail, hlast]
      rw [show
          (fullPartialSumHistory (d := d) (n := n) x) ⟨n, Finset.mem_Iic.2 le_rfl⟩ =
            Fin.partialSum (tailIncrementVector (d := d) (n := n) x) (Fin.last n) by
            rw [fullPartialSumHistory]
            by_cases h0 : n = 0
            · subst n
              simp
            · simp [h0, partialSumPath, hprevIndex]]
    simpa [tail', fullPartialSumHistory, _root_.IicProdIoc_def, hi] using
      congrArg (fun v : E ↦ v coord) hlastPath

/-- Helper for Theorem 14.28: extend the increment family by a time-`0` `dirac 0` law so that
product measures on `Iic k` simultaneously encode the fixed starting point and the increments. -/
private def fullIncrementLaw (μ : Fin n → ProbabilityMeasure E) : ℕ → ProbabilityMeasure E
  | 0 => ⟨Measure.dirac (0 : E), inferInstance⟩
  | k + 1 =>
      if hk : k < n then
        μ ⟨k, hk⟩
      else
        ⟨Measure.dirac (0 : E), inferInstance⟩

/-- Helper for Theorem 14.28: the increment histories themselves are generated by a constant kernel
family, whose step-`k` law is the `(k + 1)`-st extended increment law. -/
private def incrementTrajectoryKernel (μ : Fin n → ProbabilityMeasure E) :
    (k : ℕ) → Kernel ((i : Finset.Iic k) → E) E :=
  fun k ↦ Kernel.const _ (fullIncrementLaw (d := d) (n := n) μ (k + 1) : Measure E)

/-- Helper for Theorem 14.28: after passing to cumulative-sum histories, the next convolution
step is still just translation of the fresh increment law by the current endpoint. -/
private theorem convolutionStep_fullPartialSumHistory_apply_eq_map_add
    (μ : Fin n → ProbabilityMeasure E) {k : ℕ} (hk : k < n)
    (x : (i : Finset.Iic k) → E) :
    convolutionTrajectoryKernel μ k (fullPartialSumHistory (d := d) (n := k) x) =
      Measure.map
        (fun u : E ↦
          (fullPartialSumHistory (d := d) (n := k) x) ⟨k, Finset.mem_Iic.2 le_rfl⟩ + u)
        (μ ⟨k, hk⟩ : Measure E) := by
  -- Proof comment: this is exactly the one-step translation formula, evaluated at the cumulative
  -- sum history associated to the current increment history.
  simpa using
    convolutionStep_apply_eq_map_add (d := d) (n := n) μ hk
      (fullPartialSumHistory (d := d) (n := k) x)

/-- Helper for Theorem 14.28: on nonzero `Ioc` indices, the extended increment family agrees with
the original `Fin n`-indexed family after the canonical reindexing. -/
private theorem fullIncrementLaw_ioc_eq
    (μ : Fin n → ProbabilityMeasure E) (i : Finset.Ioc 0 n) :
    (fullIncrementLaw (d := d) (n := n) μ i.1 : Measure E) =
      (μ ((finIocEquiv (n := n)).symm i) : Measure E) := by
  have hi0 : 0 < i.1 := (Finset.mem_Ioc.1 i.2).1
  have hk : i.1 - 1 < n := ((finIocEquiv (n := n)).symm i).2
  have hsucc : i.1 = (i.1 - 1) + 1 := by
    exact (Nat.sub_eq_iff_eq_add (Nat.succ_le_of_lt hi0)).1 rfl
  rw [hsucc, fullIncrementLaw, dif_pos hk]
  simp [finIocEquiv]

/-- Helper for Theorem 14.28: the tail projection is restriction to nonzero times followed by the
canonical reindexing `Ioc 0 n ≃ Fin n`. -/
private theorem tailIncrementVector_eq_piCongrLeft_comp_restrict :
    tailIncrementVector (d := d) (n := n) =
      fun z ↦
        (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ E) (finIocEquiv (n := n)).symm)
          (restrictNonzeroHistory (d := d) (n := n) z) := by
  -- Proof comment: both maps read the same nonzero coordinates and only differ by the bookkeeping
  -- equivalence between `Fin n` and `Ioc 0 n`.
  funext z
  funext j
  let i : Finset.Ioc 0 n := (finIocEquiv (n := n)) j
  have happly :
      (MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ E) (finIocEquiv (n := n)).symm)
          (restrictNonzeroHistory (d := d) (n := n) z) j =
        restrictNonzeroHistory (d := d) (n := n) z i := by
    simpa [i] using
      (MeasurableEquiv.piCongrLeft_apply_apply
        (e := (finIocEquiv (n := n)).symm)
        (β := fun _ : Fin n ↦ E)
        (x := restrictNonzeroHistory (d := d) (n := n) z)
        (i := i))
  -- Proof comment: evaluating the reindexed restricted history at `j` reads exactly the same
  -- nonzero coordinate as `tailIncrementVector`.
  simpa [tailIncrementVector, restrictNonzeroHistory, i] using happly.symm

/-- Helper for Theorem 14.28: restricting a full cumulative-sum history to nonzero times yields
the original `partialSumPath` on the extracted increment vector. -/
private theorem restrict_fullPartialSumHistory_eq_partialSumPath_tail
    (z : (i : Finset.Iic n) → E) :
    restrictNonzeroHistory (d := d) (n := n) (fullPartialSumHistory (d := d) (n := n) z) =
      fun i ↦ partialSumPath (d := d) (n := n) (tailIncrementVector (d := d) (n := n) z) i := by
  -- Proof comment: on a nonzero time index, `fullPartialSumHistory` is defined by the same
  -- partial-sum formula as `partialSumPath`, just viewed through the restricted index set.
  ext i
  have hi0 : i.1 ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.1 i.2).1
  simp [restrictNonzeroHistory, fullPartialSumHistory, hi0]

/-- Helper for Theorem 14.28: forgetting time `0` from the full increment product law recovers
the usual `Fin n`-indexed product increment law. -/
private theorem map_tailIncrementVector_fullIncrementLaw_eq_finIncrementProduct
    (μ : Fin n → ProbabilityMeasure E) :
    (Measure.pi fun i : Finset.Iic n ↦ (fullIncrementLaw (d := d) (n := n) μ i : Measure E)).map
      (tailIncrementVector (d := d) (n := n))
      = Measure.pi fun i : Fin n ↦ (μ i : Measure E) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ E) (finIocEquiv (n := n)).symm
  have hrestrict :
      Measure.pi (fun i : Finset.Ioc 0 n ↦
        (fullIncrementLaw (d := d) (n := n) μ i.1 : Measure E)) =
        (Measure.pi fun i : Finset.Iic n ↦
          (fullIncrementLaw (d := d) (n := n) μ i : Measure E)).map
            (restrictNonzeroHistory (d := d) (n := n)) := by
    -- Proof comment: the `Ioc`-indexed increment product law is the canonical restriction of the
    -- full `Iic`-indexed product law.
    simpa [restrictNonzeroHistory] using
      (MeasureTheory.isProjectiveMeasureFamily_pi
        (fun i : ℕ ↦ (fullIncrementLaw (d := d) (n := n) μ i : Measure E))
        (Finset.Iic n) (Finset.Ioc 0 n) Ioc_subset_Iic_self)
  calc
    (Measure.pi fun i : Finset.Iic n ↦ (fullIncrementLaw (d := d) (n := n) μ i : Measure E)).map
        (tailIncrementVector (d := d) (n := n))
        =
        ((Measure.pi fun i : Finset.Iic n ↦
            (fullIncrementLaw (d := d) (n := n) μ i : Measure E)).map
            (restrictNonzeroHistory (d := d) (n := n))).map e := by
          rw [tailIncrementVector_eq_piCongrLeft_comp_restrict (d := d) (n := n)]
          rw [Measure.map_map]
          · rfl
          · exact e.measurable
          · exact measurable_restrictNonzeroHistory (d := d) (n := n)
    _ =
        (Measure.pi fun i : Finset.Ioc 0 n ↦
          (fullIncrementLaw (d := d) (n := n) μ i.1 : Measure E)).map e := by
          rw [hrestrict]
    _ =
        (Measure.pi fun i : Finset.Ioc 0 n ↦
          (μ ((finIocEquiv (n := n)).symm i) : Measure E)).map e := by
          simp_rw [fullIncrementLaw_ioc_eq (d := d) (n := n) μ]
    _ = Measure.pi fun i : Fin n ↦ (μ i : Measure E) := by
          simpa [e] using iocIncrementProduct_eq_finIncrementProduct (d := d) (n := n) μ

/-- Helper for Theorem 14.28: the finite increment vector has the product law of its marginals. -/
private theorem incrementVector_hasLaw_pi
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → E} {μ : Fin n → ProbabilityMeasure E}
    (hX_indep : iIndepFun X P) (hX_law : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω i ↦ X i ω) (Measure.pi fun i : Fin n ↦ (μ i : Measure E)) P := by
  -- Proof comment: finite independence identifies the joint pushforward with the product of the
  -- marginals, and the coordinate law hypotheses rewrite those marginals to `μ i`.
  refine ⟨aemeasurable_pi_lambda _ fun i ↦ (hX_law i).aemeasurable, ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hX_law i).aemeasurable).1 hX_indep]
  congr 1
  funext i
  exact (hX_law i).map_eq

/-- Helper for Theorem 14.28: pushing the joint increment law through the cumulative-sum map
gives the law of the partial-sum path. -/
private theorem partialSums_hasLaw_partialSumMap
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → E} {μ : Fin n → ProbabilityMeasure E}
    (hX_indep : iIndepFun X P) (hX_law : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw
      (fun ω (i : Finset.Ioc 0 n) ↦
        Fin.partialSum (fun j ↦ X j ω)
          ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 i.2).2⟩)
      (Measure.map (partialSumPath (d := d) (n := n))
        (Measure.pi fun i : Fin n ↦ (μ i : Measure E))) P := by
  have hVec :
      HasLaw (fun ω i ↦ X i ω) (Measure.pi fun i : Fin n ↦ (μ i : Measure E)) P :=
    incrementVector_hasLaw_pi (d := d) (n := n) hX_indep hX_law
  have hPath :
      HasLaw (partialSumPath (d := d) (n := n))
        (Measure.map (partialSumPath (d := d) (n := n))
          (Measure.pi fun i : Fin n ↦ (μ i : Measure E)))
        (Measure.pi fun i : Fin n ↦ (μ i : Measure E)) := by
    -- Proof comment: a measurable map has its pushforward as its own law under the source
    -- measure.
    refine ⟨(measurable_partialSumPath (d := d) (n := n)).aemeasurable, rfl⟩
  -- Proof comment: compose the increment-vector law with the cumulative-sum map.
  simpa [partialSumPath, Function.comp] using hPath.fun_comp hVec

/-- Helper for Theorem 14.28: one increment-kernel step followed by the cumulative-sum map agrees
with first taking cumulative sums and then performing the corresponding convolution step. -/
private theorem incrementTrajectorySucc_apply_eq_map_append
    (μ : Fin n → ProbabilityMeasure E) {k : ℕ} (hk : k < n)
    (x : (i : Finset.Iic k) → E) :
    partialTraj (X := fun _ : ℕ ↦ E)
      (incrementTrajectoryKernel (d := d) (n := n) μ) k (k + 1) x =
      Measure.map
        (fun u : E ↦
          _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
            (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k u))
        (μ ⟨k, hk⟩ : Measure E) := by
  -- Proof comment: expand the one-step `partialTraj`, rewrite the constant increment kernel using
  -- `fullIncrementLaw`, and collapse the resulting `dirac`-product pushforward to the history
  -- extension map.
  rw [partialTraj_succ_self]
  have hmap :
      ((Kernel.id ×ₖ
        (incrementTrajectoryKernel (d := d) (n := n) μ k).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)).map
          (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1))) x =
        Measure.map (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1))
          (((Kernel.id : Kernel ((i : Finset.Iic k) → E) ((i : Finset.Iic k) → E)) ×ₖ
            (incrementTrajectoryKernel (d := d) (n := n) μ k).map
              (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)) x) := by
        simpa using
          (Kernel.map_apply
            (κ := ((Kernel.id : Kernel ((i : Finset.Iic k) → E) ((i : Finset.Iic k) → E)) ×ₖ
              (incrementTrajectoryKernel (d := d) (n := n) μ k).map
                (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)))
            (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1))
            (hf := measurable_IicProdIoc)
            (a := x))
  rw [hmap]
  letI : IsMarkovKernel (incrementTrajectoryKernel (d := d) (n := n) μ k) := by
    rw [incrementTrajectoryKernel]
    infer_instance
  letI :
      IsMarkovKernel
        ((incrementTrajectoryKernel (d := d) (n := n) μ k).map
          (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)) :=
    IsMarkovKernel.map _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable
  rw [Kernel.prod_apply, Kernel.id_apply]
  rw [incrementTrajectoryKernel]
  rw [Kernel.map_const _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable]
  rw [Kernel.const_apply, fullIncrementLaw, dif_pos hk]
  rw [Measure.dirac_prod]
  rw [Measure.map_map measurable_IicProdIoc measurable_prodMk_left]
  have happend :
      Measurable
        ((_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)) ∘ Prod.mk x) := by
      simpa [Function.comp] using
        measurable_IicProdIoc.comp ((measurable_const).prodMk measurable_id)
  rw [Measure.map_map happend
    (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable]
  rfl

/-- Helper for Theorem 14.28: one increment-kernel step followed by the cumulative-sum map agrees
with first taking cumulative sums and then performing the corresponding convolution step. -/
private theorem fullPartialSumHistory_intertwines_incrementSucc
    (μ : Fin n → ProbabilityMeasure E) {k : ℕ} (hk : k < n)
    (x : (i : Finset.Iic k) → E) :
    partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) k (k + 1)
        (fullPartialSumHistory (d := d) (n := k) x) =
      Measure.map (fullPartialSumHistory (d := d) (n := k + 1))
        (partialTraj (X := fun _ : ℕ ↦ E)
          (incrementTrajectoryKernel (d := d) (n := n) μ) k (k + 1) x) := by
  -- Route correction: prove the successor bridge only after evaluating at a fixed prefix history,
  -- so both sides normalize to the same pushforward of `μ ⟨k, hk⟩`.
  calc
    partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) k (k + 1)
        (fullPartialSumHistory (d := d) (n := k) x) =
      Measure.map
        (fun u : E ↦
          _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
            (fullPartialSumHistory (d := d) (n := k) x,
              MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k
                ((fullPartialSumHistory (d := d) (n := k) x)
                  ⟨k, Finset.mem_Iic.2 le_rfl⟩ + u)))
        (μ ⟨k, hk⟩ : Measure E) := by
          -- Proof comment: the convolution successor step is the translated increment law
          -- inserted at the terminal coordinate of the current cumulative-sum history.
          rw [partialTraj_succ_self]
          have hmap :
              ((Kernel.id ×ₖ
                (convolutionTrajectoryKernel μ k).map
                  (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)).map
                  (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)))
                  (fullPartialSumHistory (d := d) (n := k) x) =
                Measure.map (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1))
                  (((Kernel.id : Kernel ((i : Finset.Iic k) → E) ((i : Finset.Iic k) → E)) ×ₖ
                    (convolutionTrajectoryKernel μ k).map
                      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k))
                    (fullPartialSumHistory (d := d) (n := k) x)) := by
                simpa using
                  (Kernel.map_apply
                    (κ := ((Kernel.id :
                      Kernel ((i : Finset.Iic k) → E) ((i : Finset.Iic k) → E)) ×ₖ
                      (convolutionTrajectoryKernel μ k).map
                        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)))
                    (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1))
                    (hf := measurable_IicProdIoc)
                    (a := fullPartialSumHistory (d := d) (n := k) x))
          rw [hmap]
          letI : IsMarkovKernel (convolutionTrajectoryKernel μ k) := by
            refine ⟨fun y => ?_⟩
            rw [convolutionStep_apply_eq_map_add (d := d) (n := n) μ hk y]
            exact Measure.isProbabilityMeasure_map (by fun_prop)
          letI :
              IsMarkovKernel
                ((convolutionTrajectoryKernel μ k).map
                  (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)) :=
            IsMarkovKernel.map _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable
          rw [Kernel.prod_apply, Kernel.id_apply]
          rw [Kernel.map_apply _ (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable]
          rw [convolutionStep_fullPartialSumHistory_apply_eq_map_add (d := d) (n := n) μ hk x]
          rw [Measure.dirac_prod]
          rw [Measure.map_map measurable_IicProdIoc measurable_prodMk_left]
          have happend :
              Measurable
                ((_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)) ∘
                  Prod.mk (fullPartialSumHistory (d := d) (n := k) x)) := by
              simpa [Function.comp] using
                measurable_IicProdIoc.comp ((measurable_const).prodMk measurable_id)
          rw [Measure.map_map happend
            (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable]
          have htranslate :
              Measurable
                (((_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)) ∘
                    Prod.mk (fullPartialSumHistory (d := d) (n := k) x)) ∘
                  (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)) := by
              simpa [Function.comp] using
                happend.comp
                  ((MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable)
          have hadd :
              Measurable (fun u : E ↦
                (fullPartialSumHistory (d := d) (n := k) x)
                  ⟨k, Finset.mem_Iic.2 le_rfl⟩ + u) :=
            (measurable_const).add measurable_id
          have hcomp3 :
              (((_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)) ∘
                  Prod.mk (fullPartialSumHistory (d := d) (n := k) x)) ∘
                (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k)) ∘
                  (fun u : E ↦
                    (fullPartialSumHistory (d := d) (n := k) x)
                      ⟨k, Finset.mem_Iic.2 le_rfl⟩ + u) =
                (fun u : E ↦
                  _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
                    (fullPartialSumHistory (d := d) (n := k) x,
                      MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k
                        ((fullPartialSumHistory (d := d) (n := k) x)
                          ⟨k, Finset.mem_Iic.2 le_rfl⟩ + u))) := by
              rfl
          rw [Measure.map_map htranslate hadd, hcomp3]
    _ =
      Measure.map
        (fun u : E ↦
          fullPartialSumHistory (d := d) (n := k + 1)
            (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
              (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k u)))
        (μ ⟨k, hk⟩ : Measure E) := by
          -- Proof comment: `fullPartialSumHistory_IicProdIoc` identifies extending the increment
          -- history and then summing with summing first and translating only the new endpoint.
          congr 1
          funext u
          simpa using (fullPartialSumHistory_IicProdIoc (d := d) (n := k) x u).symm
    _ =
      Measure.map (fullPartialSumHistory (d := d) (n := k + 1))
        (Measure.map
          (fun u : E ↦
            _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
              (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k u))
          (μ ⟨k, hk⟩ : Measure E)) := by
          -- Proof comment: package the shared extension map as a single source-side pushforward.
          have hcomp :
              (fun u : E ↦
                fullPartialSumHistory (d := d) (n := k + 1)
                  (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
                    (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k u))) =
                (fullPartialSumHistory (d := d) (n := k + 1)) ∘
                  (fun u : E ↦
                    _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
                      (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k u)) := by
                rfl
          have hinner :
              Measurable (fun u : E ↦
                _root_.IicProdIoc (X := fun _ : ℕ ↦ E) k (k + 1)
                  (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k u)) := by
                simpa [Function.comp] using
                  measurable_IicProdIoc.comp
                    ((measurable_const).prodMk
                      ((MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) k).measurable))
          rw [hcomp, ← Measure.map_map
            (measurable_fullPartialSumHistory (d := d) (n := k + 1))
            hinner]
    _ =
      Measure.map (fullPartialSumHistory (d := d) (n := k + 1))
        (partialTraj (X := fun _ : ℕ ↦ E)
          (incrementTrajectoryKernel (d := d) (n := n) μ) k (k + 1) x) := by
          -- Proof comment: the increment successor step is exactly the pushforward along the
          -- append-history map from the fresh increment law.
          rw [incrementTrajectorySucc_apply_eq_map_append (d := d) (n := n) μ hk x]

/-- Helper for Theorem 14.28: at the measure level, one increment step followed by
`fullPartialSumHistory` agrees with first transporting the prefix measure through
`fullPartialSumHistory` and then applying the corresponding convolution step. -/
private theorem fullPartialSumHistory_intertwines_incrementSucc_comp
    (μ : Fin n → ProbabilityMeasure E) {k : ℕ} (hk : k < n)
    (ν : Measure ((i : Finset.Iic k) → E)) :
    partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) k (k + 1) ∘ₘ
      Measure.map (fullPartialSumHistory (d := d) (n := k)) ν =
      Measure.map (fullPartialSumHistory (d := d) (n := k + 1))
        (partialTraj (X := fun _ : ℕ ↦ E)
          (incrementTrajectoryKernel (d := d) (n := n) μ) k (k + 1) ∘ₘ ν) := by
  -- Proof comment: rewrite the mapped prefix law as composition with a deterministic kernel, use
  -- the pointwise successor bridge as a kernel equality, and then move the final map back to the
  -- measure side with `Measure.map_comp`.
  rw [← Measure.deterministic_comp_eq_map
    (μ := ν) (hf := measurable_fullPartialSumHistory (d := d) (n := k))]
  rw [Measure.comp_assoc]
  rw [show
      partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) k (k + 1) ∘ₖ
        Kernel.deterministic (fullPartialSumHistory (d := d) (n := k))
          (measurable_fullPartialSumHistory (d := d) (n := k)) =
      (partialTraj (X := fun _ : ℕ ↦ E)
        (incrementTrajectoryKernel (d := d) (n := n) μ) k (k + 1)).map
          (fullPartialSumHistory (d := d) (n := k + 1)) by
        ext x s hs
        rw [Kernel.comp_deterministic_eq_comap, Kernel.comap_apply']
        rw [Kernel.map_apply' _ (measurable_fullPartialSumHistory (d := d) (n := k + 1)) _ hs]
        rw [fullPartialSumHistory_intertwines_incrementSucc (d := d) (n := n) μ hk x]
        rw [Measure.map_apply (measurable_fullPartialSumHistory (d := d) (n := k + 1)) hs]]
  rw [← Measure.map_comp
    (μ := ν)
    (κ := partialTraj (X := fun _ : ℕ ↦ E)
      (incrementTrajectoryKernel (d := d) (n := n) μ) k (k + 1))
    (hf := measurable_fullPartialSumHistory (d := d) (n := k + 1))]

/-- Helper for Theorem 14.28: the full convolution trajectory law started at `0` is the
pushforward of the increment trajectory law by the cumulative-sum map on full histories. -/
private theorem convolutionTrajectoryLaw_eq_map_incrementTrajectoryLaw
    (μ : Fin n → ProbabilityMeasure E) :
    ∀ {k : ℕ}, k ≤ n →
      partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 k ∘ₘ
        Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)) =
      Measure.map (fullPartialSumHistory (d := d) (n := k))
        (partialTraj (X := fun _ : ℕ ↦ E)
          (incrementTrajectoryKernel (d := d) (n := n) μ) 0 k ∘ₘ
          Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)))
  | 0, _ => by
      -- Proof comment: the base case is the unique zero history on `Iic 0`.
      rw [partialTraj_self, MeasureTheory.Measure.id_comp]
      rw [partialTraj_self, MeasureTheory.Measure.id_comp]
      rw [Measure.map_dirac' (measurable_fullPartialSumHistory (d := d) (n := 0))]
      -- Proof comment: the cumulative-sum history on the unique time-`0` path is still the same
      -- zero path.
      congr 1
      ext i
      have hi : i.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.1 i.2)
      simp [fullPartialSumHistory, hi]
  | k + 1, hk1 => by
      have hk : k < n := Nat.lt_of_succ_le hk1
      have ih :
          partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 k ∘ₘ
            Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)) =
          Measure.map (fullPartialSumHistory (d := d) (n := k))
            (partialTraj (X := fun _ : ℕ ↦ E)
              (incrementTrajectoryKernel (d := d) (n := n) μ) 0 k ∘ₘ
              Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))) :=
        convolutionTrajectoryLaw_eq_map_incrementTrajectoryLaw
          (μ := μ) (k := k) (Nat.le_of_succ_le hk1)
      -- Proof comment: factor the successor law at time `k`, replace the prefix measure by the
      -- induction hypothesis, and use the one-step transport lemma once.
      rw [partialTraj_succ_eq_comp
        (X := fun _ : ℕ ↦ E) (κ := convolutionTrajectoryKernel μ) (a := 0) (b := k)
        (Nat.zero_le k)]
      rw [← Measure.comp_assoc, ih]
      rw [fullPartialSumHistory_intertwines_incrementSucc_comp (d := d) (n := n) μ hk]
      congr 1
      rw [Measure.comp_assoc]
      rw [← partialTraj_succ_eq_comp
        (X := fun _ : ℕ ↦ E)
        (κ := incrementTrajectoryKernel (d := d) (n := n) μ)
        (a := 0) (b := k) (Nat.zero_le k)]

/-- Helper for Theorem 14.28: restricting the full cumulative-sum history pushforward is the same
as first forgetting time `0` from the increment history and then applying `partialSumPath`. -/
private theorem restrictFullPartialSumHistory_pushforward_eq_partialSumPath_pushforward
    (ν : Measure ((i : Finset.Iic n) → E)) :
    Measure.map (restrictNonzeroHistory (d := d) (n := n))
      (Measure.map (fullPartialSumHistory (d := d) (n := n)) ν) =
      Measure.map (partialSumPath (d := d) (n := n))
        (Measure.map (tailIncrementVector (d := d) (n := n)) ν) := by
  -- Proof comment: rewrite both sides as a single pushforward from the same source measure and
  -- then use the pointwise identity
  -- `restrictNonzeroHistory ∘ fullPartialSumHistory = partialSumPath ∘ tailIncrementVector`.
  rw [Measure.map_map
    (measurable_restrictNonzeroHistory (d := d) (n := n))
    (measurable_fullPartialSumHistory (d := d) (n := n))]
  rw [Measure.map_map
    (measurable_partialSumPath (d := d) (n := n))
    (measurable_tailIncrementVector (d := d) (n := n))]
  congr 1
  funext z
  funext i
  simpa [Function.comp] using
    congrFun (restrict_fullPartialSumHistory_eq_partialSumPath_tail (d := d) (n := n) z) i

/-- Helper for Theorem 14.28: the increment trajectory law started from the unique zero history
has the expected product law on the increment vector indexed by `Fin n`. -/
private theorem map_tailIncrementVector_incrementTrajectoryLaw_eq_finIncrementProduct
    (μ : Fin n → ProbabilityMeasure E) :
    (partialTraj (X := fun _ : ℕ ↦ E)
      (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
      Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))).map
        (tailIncrementVector (d := d) (n := n)) =
      Measure.pi fun i : Fin n ↦ (μ i : Measure E) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n ↦ E) (finIocEquiv (n := n)).symm
  have hrestrict :
      (partialTraj (X := fun _ : ℕ ↦ E)
        (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
        Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))).map
          (restrictNonzeroHistory (d := d) (n := n)) =
        Measure.pi (fun i : Finset.Ioc 0 n ↦
          (fullIncrementLaw (d := d) (n := n) μ i.1 : Measure E)) := by
    -- Proof comment: the increment trajectory is generated by a constant kernel, so after
    -- restricting away the fixed time-`0` coordinate it is exactly the `Ioc 0 n` product law.
    rw [MeasureTheory.Measure.map_comp
      (μ := Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)))
      (κ := partialTraj (X := fun _ : ℕ ↦ E)
        (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n)
      (hf := measurable_restrictNonzeroHistory (d := d) (n := n))]
    rw [show
        (partialTraj (X := fun _ : ℕ ↦ E)
          (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n).map
            (restrictNonzeroHistory (d := d) (n := n)) =
          Kernel.const ((i : Finset.Iic 0) → E)
            (Measure.pi fun i : Finset.Ioc 0 n ↦
              (fullIncrementLaw (d := d) (n := n) μ i.1 : Measure E)) by
          simpa [incrementTrajectoryKernel, restrictNonzeroHistory] using
            (partialTraj_const_restrict₂
              (X := fun _ : ℕ ↦ E)
              (μ := fun i : ℕ ↦ (fullIncrementLaw (d := d) (n := n) μ i : Measure E))
              (a := 0) (b := n))]
    rw [Measure.const_comp]
    simp
  calc
    (partialTraj (X := fun _ : ℕ ↦ E)
      (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
      Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))).map
        (tailIncrementVector (d := d) (n := n))
        =
      ((partialTraj (X := fun _ : ℕ ↦ E)
        (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
        Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))).map
          (restrictNonzeroHistory (d := d) (n := n))).map e := by
            rw [tailIncrementVector_eq_piCongrLeft_comp_restrict (d := d) (n := n)]
            rw [Measure.map_map]
            · rfl
            · exact e.measurable
            · exact measurable_restrictNonzeroHistory (d := d) (n := n)
    _ =
      (Measure.pi fun i : Finset.Ioc 0 n ↦
        (fullIncrementLaw (d := d) (n := n) μ i.1 : Measure E)).map e := by
          rw [hrestrict]
    _ =
      (Measure.pi fun i : Finset.Ioc 0 n ↦
        (μ ((finIocEquiv (n := n)).symm i) : Measure E)).map e := by
          simp_rw [fullIncrementLaw_ioc_eq (d := d) (n := n) μ]
    _ = Measure.pi fun i : Fin n ↦ (μ i : Measure E) := by
          simpa [e] using iocIncrementProduct_eq_finIncrementProduct (d := d) (n := n) μ

/-- Helper for Theorem 14.28: starting the comapped path kernel at `0` is the same as starting
the full-history path kernel at the unique zero history on `Iic 0`. -/
private theorem convolutionPathStart_comap_eq_zeroHistory
    (μ : Fin n → ProbabilityMeasure E) :
    let e0 : E ≃ᵐ ((i : Finset.Iic 0) → E) :=
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm
    let K : Kernel ((i : Finset.Iic 0) → E) ((i : Finset.Ioc 0 n) → E) :=
      (partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 n).map
        (Finset.restrict₂ (π := fun _ : ℕ ↦ E) Ioc_subset_Iic_self)
    K.comap (fun x : E ↦ e0 x) (by simpa using e0.measurable) ∘ₘ Measure.dirac (0 : E) =
      K ∘ₘ Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)) := by
  dsimp
  let e0 : E ≃ᵐ ((i : Finset.Iic 0) → E) :=
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm
  let K : Kernel ((i : Finset.Iic 0) → E) ((i : Finset.Ioc 0 n) → E) :=
    (partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 n).map
      (Finset.restrict₂ (π := fun _ : ℕ ↦ E) Ioc_subset_Iic_self)
  change Kernel.comap K (fun x : E ↦ e0 x) (by simpa [e0] using e0.measurable) ∘ₘ
      Measure.dirac (0 : E) =
    K ∘ₘ Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))
  -- Proof comment: rewrite the comap as kernel composition with a deterministic initial-state map,
  -- then evaluate that deterministic start map on the `dirac` mass at `0`.
  rw [← Kernel.comp_deterministic_eq_comap (κ := K) (g := fun x : E ↦ e0 x)]
  rw [← MeasureTheory.Measure.comp_assoc]
  rw [MeasureTheory.Measure.deterministic_comp_eq_map
    (μ := Measure.dirac (0 : E)) (hf := by simpa [e0] using e0.measurable)]
  rw [Measure.map_dirac' (by simpa [e0] using e0.measurable)]
  rw [show e0 (0 : E) = (fun _ : Finset.Iic 0 ↦ (0 : E)) by
    ext i
    simp [e0]]

/-- Helper for Theorem 14.28: the path law generated by the convolution kernels from `0` is the
pushforward of the product increment law by the cumulative-sum map. -/
private theorem convolutionTrajectoryLaw_eq_partialSumMap
    (μ : Fin n → ProbabilityMeasure E) :
    let state : ℕ → Type _ := fun _ ↦ E
    let κstep : (k : ℕ) → Kernel ((i : Finset.Iic k) → state i) (state (k + 1)) :=
      convolutionTrajectoryKernel μ
    let e : state 0 ≃ᵐ ((i : Finset.Iic 0) → state i) :=
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ state i)).symm
    let κpath : Kernel (state 0) ((i : Finset.Ioc 0 n) → state i) :=
      Kernel.comap
        ((partialTraj κstep 0 n).map (restrict₂ Ioc_subset_Iic_self))
        (fun x : state 0 ↦ e x)
        (by simpa using e.measurable)
    κpath ∘ₘ Measure.dirac (0 : state 0) =
      Measure.map (partialSumPath (d := d) (n := n))
        (Measure.pi fun i : Fin n ↦ (μ i : Measure E)) := by
  -- Route correction: instead of normalizing the successor step against an explicit `Measure.pi`
  -- at each induction stage, transport the convolution trajectory law through the constant
  -- increment kernel and use the product-measure normalization only once at the end.
  -- Proof comment: after replacing the start state by the unique `Iic 0` history, the intended
  -- proof composes `convolutionTrajectoryLaw_eq_map_incrementTrajectoryLaw` with
  -- `restrict_fullPartialSumHistory_eq_partialSumPath_tail`,
  -- `convolutionPathStart_comap_eq_zeroHistory`, and the closing increment-law theorem
  -- `map_tailIncrementVector_incrementTrajectoryLaw_eq_finIncrementProduct`.
  -- Proof comment: replace the starting point `0` by the unique zero history on `Iic 0`, then
  -- successively push the law through the full-history cumulative-sum map, the nonzero-time
  -- restriction, and finally the increment product law.
  dsimp
  calc
    Kernel.comap
        ((partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 n).map
          (Finset.restrict₂ (π := fun _ : ℕ ↦ E) Ioc_subset_Iic_self))
        (fun x : E ↦ ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ E)).symm) x)
        (by
          simpa using
            ((MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ E)).symm.measurable))
        ∘ₘ Measure.dirac (0 : E) =
      ((partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 n).map
        (restrictNonzeroHistory (d := d) (n := n))) ∘ₘ
          Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)) := by
            simpa [restrictNonzeroHistory] using
              convolutionPathStart_comap_eq_zeroHistory (d := d) (n := n) μ
    _ =
      Measure.map (restrictNonzeroHistory (d := d) (n := n))
        (partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 n ∘ₘ
          Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))) := by
            rw [← Measure.map_comp
              (μ := Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)))
              (κ := partialTraj (X := fun _ : ℕ ↦ E) (convolutionTrajectoryKernel μ) 0 n)
              (hf := measurable_restrictNonzeroHistory (d := d) (n := n))]
    _ =
      Measure.map (restrictNonzeroHistory (d := d) (n := n))
        (Measure.map (fullPartialSumHistory (d := d) (n := n))
          (partialTraj (X := fun _ : ℕ ↦ E)
            (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
            Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)))) := by
              rw [convolutionTrajectoryLaw_eq_map_incrementTrajectoryLaw
                (d := d) (n := n) μ (k := n) le_rfl]
    _ =
      Measure.map (partialSumPath (d := d) (n := n))
        (Measure.map (tailIncrementVector (d := d) (n := n))
          (partialTraj (X := fun _ : ℕ ↦ E)
            (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
            Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E)))) := by
              simpa using
                (restrictFullPartialSumHistory_pushforward_eq_partialSumPath_pushforward
                  (d := d) (n := n)
                  (ν := partialTraj (X := fun _ : ℕ ↦ E)
                    (incrementTrajectoryKernel (d := d) (n := n) μ) 0 n ∘ₘ
                    Measure.dirac (fun _ : Finset.Iic 0 ↦ (0 : E))))
    _ =
      Measure.map (partialSumPath (d := d) (n := n))
        (Measure.pi fun i : Fin n ↦ (μ i : Measure E)) := by
          rw [map_tailIncrementVector_incrementTrajectoryLaw_eq_finIncrementProduct
            (d := d) (n := n) μ]

-- Proof sketch: first identify the left-hand side with the `Kernel.partialTraj`-generated law of
-- the finite path `(S₁, ..., Sₙ)` through the canonical kernel on starting states obtained from
-- `Kernel.partialTraj` by forgetting time `0`. Then rewrite that law as the pushforward of the
-- product law of the increments under the cumulative-sum map. Next use independence and the law
-- assumptions to identify that product law with the joint law of `(X₀, ..., Xₙ₋₁)`, and finally
-- push forward by `Fin.partialSum` along the source-facing index set `{1, ..., n}`.
/-- Theorem 14.28: for independent `ℝ^d`-valued increments with laws `μ i`, the path law generated
by the convolution kernels and started at `0` agrees with the joint law of the partial sums. Here
the owner kernel is the finite-step `Kernel.partialTraj` law, restricted from `Iic n` to the
source-facing index set `Finset.Ioc 0 n` representing the textbook partial sums `S₁, …, Sₙ`. -/
theorem convolutionTrajectoryLaw_eq_jointLaw_partialSums
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Fin n → Ω → E} {μ : Fin n → ProbabilityMeasure E}
    (hX_indep : iIndepFun X P) (hX_law : ∀ i, HasLaw (X i) (μ i) P) :
    let state : ℕ → Type _ := fun _ ↦ E
    let κstep : (k : ℕ) → Kernel ((i : Finset.Iic k) → state i) (state (k + 1)) :=
      convolutionTrajectoryKernel μ
    let e : state 0 ≃ᵐ ((i : Finset.Iic 0) → state i) :=
      (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ state i)).symm
    let κpath : Kernel (state 0) ((i : Finset.Ioc 0 n) → state i) :=
      Kernel.comap
        ((partialTraj κstep 0 n).map (restrict₂ Ioc_subset_Iic_self))
        (fun x : state 0 ↦ e x)
        (by simpa using e.measurable)
    κpath ∘ₘ Measure.dirac (0 : state 0) =
      Measure.map
        (fun ω (i : Finset.Ioc 0 n) ↦
          Fin.partialSum (fun j ↦ X j ω)
            ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 i.2).2⟩)
        P := by
  -- Proof comment: both measures are identified with the same pushforward of the product law of
  -- the increments under the cumulative-sum map.
  calc
    (let state : ℕ → Type _ := fun _ ↦ E
      let κstep : (k : ℕ) → Kernel ((i : Finset.Iic k) → state i) (state (k + 1)) :=
        convolutionTrajectoryKernel μ
      let e : state 0 ≃ᵐ ((i : Finset.Iic 0) → state i) :=
        (MeasurableEquiv.piUnique (fun i : Finset.Iic 0 ↦ state i)).symm
      let κpath : Kernel (state 0) ((i : Finset.Ioc 0 n) → state i) :=
        Kernel.comap
          ((partialTraj κstep 0 n).map (restrict₂ Ioc_subset_Iic_self))
          (fun x : state 0 ↦ e x)
          (by simpa using e.measurable)
      κpath ∘ₘ Measure.dirac (0 : state 0))
        = Measure.map (partialSumPath (d := d) (n := n))
            (Measure.pi fun i : Fin n ↦ (μ i : Measure E)) := by
              simpa using convolutionTrajectoryLaw_eq_partialSumMap (d := d) (n := n) μ
    _ = Measure.map
          (fun ω (i : Finset.Ioc 0 n) ↦
            Fin.partialSum (fun j ↦ X j ω)
              ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Ioc.1 i.2).2⟩)
          P := by
            simpa [partialSumPath] using
              (partialSums_hasLaw_partialSumMap (d := d) (n := n)
                (P := P) (X := X) (μ := μ) hX_indep hX_law).map_eq.symm

end

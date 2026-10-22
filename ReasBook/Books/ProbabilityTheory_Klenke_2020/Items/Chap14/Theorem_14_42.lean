/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Remark_8_26
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_39
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_36

-- Declarations for this item will be appended below by the statement pipeline.

open Finset MeasureTheory ProbabilityTheory Preorder
open ProbabilityTheory.Kernel
open scoped ProbabilityTheory

noncomputable section

universe u v

section FiniteDimensional

variable {I : Type u} [Preorder I]
variable {E : Type v} [MeasurableSpace E]

/-- The projection of a path in `I → E` to the finite chain of times encoded by `j`. -/
def finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    (I → E) → Π _ : Finset.Iic n, E :=
  fun ω k ↦ ω (j k)

-- Proof sketch: each coordinate of `finiteCoordinateProjection j` is an evaluation map on the
-- product measurable space, so measurability follows coordinatewise.
/-- The projection to a finite chain of coordinates is measurable. -/
theorem measurable_finiteCoordinateProjection {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    Measurable (finiteCoordinateProjection j : (I → E) → Π _ : Finset.Iic n, E) := by
  -- Proof comment: each finite coordinate is just evaluation on the product path space.
  refine measurable_pi_lambda _ ?_
  intro k
  exact measurable_pi_apply (j k)

private def historyHead {n : ℕ} : (Π _ : Finset.Iic n, E) → E :=
  fun x ↦ x ⟨0, mem_Iic.2 (Nat.zero_le n)⟩

private theorem measurable_historyHead {n : ℕ} :
    Measurable (historyHead : (Π _ : Finset.Iic n, E) → E) := by
  -- Proof comment: the head of the history tuple is a single coordinate projection.
  simpa [historyHead] using
    measurable_pi_apply ((⟨0, mem_Iic.2 (Nat.zero_le n)⟩ : Finset.Iic n))

private def historyLast {n : ℕ} : (Π _ : Finset.Iic n, E) → E :=
  fun x ↦ x ⟨n, mem_Iic.2 le_rfl⟩

private theorem measurable_historyLast {n : ℕ} :
    Measurable (historyLast : (Π _ : Finset.Iic n, E) → E) := by
  -- Proof comment: the terminal history state is again a coordinate projection.
  simpa [historyLast] using
    measurable_pi_apply ((⟨n, mem_Iic.2 le_rfl⟩ : Finset.Iic n))

private def initialHistory : E → Π _ : Finset.Iic 0, E :=
  fun x _ ↦ x

private theorem measurable_initialHistory :
    Measurable (initialHistory : E → Π _ : Finset.Iic 0, E) := by
  -- Proof comment: on the singleton index type, the initial history map is coordinatewise `id`.
  refine measurable_pi_lambda _ ?_
  intro i
  simpa [initialHistory] using measurable_id

private noncomputable def consistentFamilyHistoryKernels
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E :=
  fun m ↦
    if hm : m < n then
      Kernel.comap
        (κ (hj (show (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)))
        historyLast measurable_historyLast
    else
      Kernel.deterministic historyHead measurable_historyHead

private noncomputable def consistentFamilyHistoryTraj {n : ℕ}
    (κhist : (m : ℕ) → Kernel (Π _ : Finset.Iic m, E) E) :
    Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E) :=
  ((@partialTraj (fun _ : ℕ ↦ E) _ κhist 0 n) :
    Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E))

/-- The finite-dimensional kernel attached to the ordered chain of kernels picked out by `j`,
viewed as a stochastic kernel in the initial state. This is the owner construction over
`Kernel.partialTraj`; the measure-valued finite-dimensional laws are obtained from it by
composition with an initial law. -/
noncomputable def consistentFamilyFiniteDimensionalKernel
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    Kernel E (Π _ : Finset.Iic n, E) :=
  consistentFamilyHistoryTraj (consistentFamilyHistoryKernels κ j hj) ∘ₖ
    Kernel.deterministic initialHistory measurable_initialHistory

/-- The finite-dimensional law attached to an initial measure `μ` and the ordered chain of kernels
picked out by `j`. This is the bridge/view API obtained from
`consistentFamilyFiniteDimensionalKernel` by composing with the initial law. -/
noncomputable def consistentFamilyFiniteDimensionalMeasure
    (μ : Measure E) (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    Measure (Π _ : Finset.Iic n, E) :=
  consistentFamilyFiniteDimensionalKernel κ j hj ∘ₘ μ

-- Proof sketch: unfold `consistentFamilyFiniteDimensionalMeasure`; when `n = 0`,
-- `partialTraj ... 0 0` is the identity kernel, so only the pushforward along the unique
-- one-point-history equivalence remains.
/-- At level `n = 0`, the finite-dimensional law is just the initial law viewed on the
one-point-history space. -/
theorem consistentFamilyFiniteDimensionalMeasure_zero
    (μ : Measure E) (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (j : Π _ : Finset.Iic 0, I) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalMeasure μ κ j hj =
      μ.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm := by
  have hinitial :
      initialHistory = (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ E)).symm := by
    funext x i
    simp [initialHistory]
  -- Proof comment: `partialTraj ... 0 0` is the identity kernel, so only the initial-history
  -- pushforward remains.
  rw [consistentFamilyFiniteDimensionalMeasure, consistentFamilyFiniteDimensionalKernel,
    ← Measure.comp_assoc]
  rw [consistentFamilyHistoryTraj, ProbabilityTheory.Kernel.partialTraj_self, Measure.id_comp]
  rw [Measure.deterministic_comp_eq_map]
  rw [hinitial]

/-- Evaluating the finite-dimensional kernel at `x` recovers the finite-dimensional law with
initial distribution `δ_x`. -/
theorem consistentFamilyFiniteDimensionalKernel_apply
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E) (x : E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    consistentFamilyFiniteDimensionalKernel κ j hj x =
      consistentFamilyFiniteDimensionalMeasure (Measure.dirac x) κ j hj := by
  -- Proof comment: composing a kernel with the Dirac mass at `x` evaluates the kernel at `x`.
  have hMeas :
      AEMeasurable (consistentFamilyFiniteDimensionalKernel κ j hj) (Measure.dirac x) :=
    (consistentFamilyFiniteDimensionalKernel κ j hj).aemeasurable
  ext s hs
  rw [consistentFamilyFiniteDimensionalMeasure, Measure.bind_apply hs hMeas]
  simpa using
    (lintegral_dirac' x ((consistentFamilyFiniteDimensionalKernel κ j hj).measurable_coe hs)).symm

/-- The finite-dimensional kernel attached to an ordered chain of Markov kernels is itself
Markov. -/
theorem consistentFamilyFiniteDimensionalKernel_isMarkov
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (κ hst)) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) := by
  let κhist := consistentFamilyHistoryKernels κ j hj
  have hκhist : ∀ m, IsMarkovKernel (κhist m) := by
    intro m
    dsimp [κhist, consistentFamilyHistoryKernels]
    split_ifs with hm
    · let hstep :
          j (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
            j ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ := by
          exact hj (show
            (⟨m, mem_Iic.2 (Nat.le_of_lt hm)⟩ : Finset.Iic n) <
              ⟨m + 1, mem_Iic.2 (Nat.succ_le_of_lt hm)⟩ from Nat.lt_succ_self m)
      -- Proof comment: on a genuine transition step, the history kernel is the given Markov
      -- kernel pulled back along the measurable last-coordinate map.
      letI : IsMarkovKernel (κ hstep) := hMarkov hstep
      simpa [hstep] using
        (inferInstance :
          IsMarkovKernel (Kernel.comap (κ hstep) historyLast measurable_historyLast))
    · -- Proof comment: after the terminal time, the history kernel is the deterministic head map.
      simpa using
        (inferInstance : IsMarkovKernel
          (Kernel.deterministic historyHead measurable_historyHead))
  letI : ∀ m, IsMarkovKernel (κhist m) := hκhist
  let κtraj :
      Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E) :=
    ((@partialTraj (fun _ : ℕ ↦ E) _ κhist 0 n) :
      Kernel (Π _ : Finset.Iic 0, E) (Π _ : Finset.Iic n, E))
  letI : IsMarkovKernel κtraj := by
    dsimp [κtraj]
    infer_instance
  -- Proof comment: `partialTraj` preserves the Markov property, and composing with the
  -- deterministic initial-history kernel keeps the full finite-dimensional law Markov.
  simpa [consistentFamilyFiniteDimensionalKernel, consistentFamilyHistoryTraj, κhist, κtraj] using
    (inferInstance :
      IsMarkovKernel
        (κtraj ∘ₖ
          Kernel.deterministic initialHistory measurable_initialHistory))

/-- Evaluating a finite-dimensional Markov kernel on a measurable set is measurable in the initial
state. -/
theorem measurable_consistentFamilyFiniteDimensionalKernel_apply
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (κ hst)) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j)
    {s : Set (Π _ : Finset.Iic n, E)} (hs : MeasurableSet s) :
    Measurable (fun x ↦ consistentFamilyFiniteDimensionalKernel κ j hj x s) := by
  have hKernelMarkov :
      IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov κ hMarkov j hj
  letI : IsMarkovKernel (consistentFamilyFiniteDimensionalKernel κ j hj) := hKernelMarkov
  -- Proof comment: this is the owner measurability of evaluations of a Markov kernel.
  simpa using Kernel.measurable_coe (consistentFamilyFiniteDimensionalKernel κ j hj) hs

end FiniteDimensional

section

variable {E : Type v} [MeasurableSpace E]
variable {I : Set NNReal}
variable [StandardBorelSpace E]
variable (h0I : (0 : NNReal) ∈ I)

/-- Helper for Theorem 14.42: convert `Finset.Iic n` to `Fin (n + 1)` by forgetting the upper-bound
proof. -/
private def iicToFinLocal (n : ℕ) : Finset.Iic n → Fin (n + 1) :=
  fun i ↦ ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

/-- Helper for Theorem 14.42: convert `Fin (n + 1)` back to `Finset.Iic n`. -/
private def finToIicLocal (n : ℕ) : Fin (n + 1) → Finset.Iic n :=
  fun i ↦ ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩

/-- Helper for Theorem 14.42: `finToIicLocal` inverts `iicToFinLocal`. -/
private theorem finToIicLocal_leftInv (n : ℕ) :
    Function.LeftInverse (finToIicLocal n) (iicToFinLocal n) := by
  intro i
  cases i
  rfl

/-- Helper for Theorem 14.42: `iicToFinLocal` inverts `finToIicLocal`. -/
private theorem finToIicLocal_rightInv (n : ℕ) :
    Function.RightInverse (finToIicLocal n) (iicToFinLocal n) := by
  intro i
  cases i
  rfl

/-- Helper for Theorem 14.42: the coordinate-forgetting map preserves the order relation on
`Finset.Iic n`. -/
private theorem iicToFinLocal_map_rel_iff (n : ℕ) {i j : Finset.Iic n} :
    iicToFinLocal n i ≤ iicToFinLocal n j ↔ i ≤ j := by
  rfl

/-- Helper for Theorem 14.42: `Finset.Iic n` is canonically order-isomorphic to `Fin (n + 1)`. -/
private def iicOrderIsoFinLocal (n : ℕ) : Finset.Iic n ≃o Fin (n + 1) where
  toFun := iicToFinLocal n
  invFun := finToIicLocal n
  left_inv := finToIicLocal_leftInv n
  right_inv := finToIicLocal_rightInv n
  map_rel_iff' := iicToFinLocal_map_rel_iff n

/-- Helper for Theorem 14.42: a finite set containing `⊥` is nonempty. -/
private theorem finiteSetNonemptyOfBotMem [OrderBot I] (J : Finset I) (hJ0 : ⊥ ∈ J) :
    J.Nonempty :=
  ⟨⊥, hJ0⟩

/-- Helper for Theorem 14.42: a finite set containing `⊥` can be read as an ordered chain of
length `J.card`. -/
private noncomputable def orderedFiniteSetOrderIso [OrderBot I] (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Finset.Iic (J.card - 1) ≃o ↥J :=
  ((iicOrderIsoFinLocal (J.card - 1)).trans
      (Fin.castOrderIso
        (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (finiteSetNonemptyOfBotMem J hJ0))))).trans
    (J.orderIsoOfFin rfl)

/-- Helper for Theorem 14.42: the increasing chain attached to a finite subset containing `⊥`. -/
private noncomputable def orderedFiniteSetChain [OrderBot I] (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Π _ : Finset.Iic (J.card - 1), I :=
  fun i ↦ (orderedFiniteSetOrderIso J hJ0 i : I)

/-- Helper for Theorem 14.42: the ordered-chain parametrization of a finite subset is strict. -/
private theorem orderedFiniteSetChain_strictMono [OrderBot I] (J : Finset I) (hJ0 : ⊥ ∈ J) :
    StrictMono (orderedFiniteSetChain J hJ0) := by
  -- Proof comment: the ordered chain is the coercion of the order isomorphism above.
  simpa [orderedFiniteSetChain] using (orderedFiniteSetOrderIso J hJ0).strictMono

/-- Helper for Theorem 14.42: the ordered chain of a finite set containing `⊥` starts at `⊥`. -/
private theorem orderedFiniteSetChain_zero [OrderBot I] (J : Finset I) (hJ0 : ⊥ ∈ J) :
    orderedFiniteSetChain J hJ0 ⟨0, Finset.mem_Iic.2 (Nat.zero_le (J.card - 1))⟩ = ⊥ := by
  have hJne : J.Nonempty := finiteSetNonemptyOfBotMem J hJ0
  have hmin : J.min' hJne = ⊥ := by
    rw [Finset.min'_eq_iff]
    exact ⟨hJ0, fun b hb ↦ bot_le⟩
  let i0 : Finset.Iic (J.card - 1) :=
    ⟨0, Finset.mem_Iic.2 (Nat.zero_le (J.card - 1))⟩
  have hi0_mem : orderedFiniteSetChain J hJ0 i0 ∈ J := by
    exact (orderedFiniteSetOrderIso J hJ0 i0).2
  have hi0_least : ∀ b : I, b ∈ J → orderedFiniteSetChain J hJ0 i0 ≤ b := by
    intro b hb
    simpa [orderedFiniteSetChain] using
      (orderedFiniteSetOrderIso J hJ0).monotone
        (show i0 ≤ (orderedFiniteSetOrderIso J hJ0).symm ⟨b, hb⟩ from Nat.zero_le _)
  have hi0_eq_min : orderedFiniteSetChain J hJ0 i0 = J.min' hJne := by
    exact ((Finset.min'_eq_iff (s := J) (H := hJne) (a := orderedFiniteSetChain J hJ0 i0)).2
      ⟨hi0_mem, hi0_least⟩).symm
  -- Proof comment: the first point of the ordered enumeration is the minimum of `J`, which is
  -- exactly `⊥` because `⊥ ∈ J`.
  exact hi0_eq_min.trans hmin

/-- Helper for Theorem 14.42: inclusion of finite subsets induces the obvious subtype embedding. -/
private def finiteSetSubtypeEmbedding {L J : Finset I} (hLJ : L ⊆ J) : ↥L ↪o ↥J where
  toFun x := ⟨x.1, hLJ x.2⟩
  inj' := by
    intro x y hxy
    cases x
    cases y
    cases hxy
    rfl
  map_rel_iff' := by
    intro x y
    rfl

/-- Helper for Theorem 14.42: a subset of a finite ordered chain is itself read off by a
bottom-preserving order embedding between the corresponding `Iic` index sets. -/
private noncomputable def orderedFiniteSetSubsetEmbedding [OrderBot I]
    (L J : Finset I) (hLJ : L ⊆ J) (hL0 : ⊥ ∈ L) (hJ0 : ⊥ ∈ J) :
    Finset.Iic (L.card - 1) ↪o Finset.Iic (J.card - 1) :=
  ((orderedFiniteSetOrderIso L hL0).toOrderEmbedding.trans
      (finiteSetSubtypeEmbedding hLJ)).trans
    (orderedFiniteSetOrderIso J hJ0).symm.toOrderEmbedding

/-- Helper for Theorem 14.42: evaluating the ordered chain of `J` along the canonical subset
embedding recovers the ordered chain of `L`. -/
private theorem orderedFiniteSetChain_comp_subsetEmbedding [OrderBot I]
    (L J : Finset I) (hLJ : L ⊆ J) (hL0 : ⊥ ∈ L) (hJ0 : ⊥ ∈ J) :
    ∀ i : Finset.Iic (L.card - 1),
      orderedFiniteSetChain J hJ0 (orderedFiniteSetSubsetEmbedding L J hLJ hL0 hJ0 i) =
        orderedFiniteSetChain L hL0 i := by
  intro i
  -- Proof comment: the subset embedding is defined by passing through the two ordered-set
  -- identifications, so applying the `J`-chain cancels the final inverse order isomorphism.
  simp [orderedFiniteSetSubsetEmbedding, orderedFiniteSetChain, finiteSetSubtypeEmbedding]

/-- Helper for Theorem 14.42: restricting the ordered `J`-tuple to `L` is the same as first
projecting to the ordered subchain corresponding to `L`. -/
private theorem restrict_orderedFiniteSetTuple_eq_comp_orderedSubchainProjection [OrderBot I]
    (L J : Finset I) (hLJ : L ⊆ J) (hL0 : ⊥ ∈ L) (hJ0 : ⊥ ∈ J) :
    (Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) ∘
        (fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
          fun j : J ↦ z ((orderedFiniteSetOrderIso J hJ0).symm j)) =
      (fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
        fun i : L ↦
          z (orderedFiniteSetSubsetEmbedding L J hLJ hL0 hJ0
            ((orderedFiniteSetOrderIso L hL0).symm i))) := by
  -- Proof comment: both descriptions pick the same `J`-coordinate for each `i : L`; the new
  -- statement isolates that transport before any measure argument is attempted.
  funext z i
  simp [orderedFiniteSetSubsetEmbedding, finiteSetSubtypeEmbedding]

/-- Helper for Theorem 14.42: the ordered-subchain coordinate projection is measurable. -/
private theorem measurable_orderedSubchainProjection [OrderBot I]
    (L J : Finset I) (hLJ : L ⊆ J) (hL0 : ⊥ ∈ L) (hJ0 : ⊥ ∈ J) :
    Measurable
      (fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
        fun i : Finset.Iic (L.card - 1) ↦
          z (orderedFiniteSetSubsetEmbedding L J hLJ hL0 hJ0 i)) := by
  -- Proof comment: every coordinate of the subchain projection is just one coordinate of the
  -- larger ordered tuple.
  refine measurable_pi_lambda _ ?_
  intro i
  exact measurable_pi_apply (orderedFiniteSetSubsetEmbedding L J hLJ hL0 hJ0 i)

/-- Helper for Theorem 14.42: the last coordinate on an `Iic m`-indexed history is measurable. -/
private theorem measurable_lastIicCoordinate {m : ℕ} :
    Measurable (fun z : Π _ : Finset.Iic m, E ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩) := by
  exact measurable_pi_apply _

/-- Helper for Theorem 14.42: the first coordinate on an `Iic m`-indexed history is measurable. -/
private theorem measurable_zeroIicCoordinate {m : ℕ} :
    Measurable
      (fun z : Π _ : Finset.Iic m, E ↦ z ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩) := by
  exact measurable_pi_apply _

/-- Helper for Theorem 14.42: in `Finset.Iic (m + 1)`, the last prefix index is strictly below
the terminal index. -/
private theorem lastIic_lt_succLast (m : ℕ) :
    (⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ : Finset.Iic (m + 1)) <
      ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := by
  -- Proof comment: this is the subtype version of `m < m + 1`.
  simpa using (Nat.lt_succ_self m)

/-- Helper for Theorem 14.42: split a successor history into its prefix and final state. -/
private noncomputable def succHistoryEquivLocal (m : ℕ) :
    (Π _ : Finset.Iic (m + 1), E) ≃ᵐ ((Π _ : Finset.Iic m, E) × E) :=
  (MeasurableEquiv.IicProdIoc (X := fun _ : ℕ ↦ E) (Nat.le_succ m)).symm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _)
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m).symm)

/-- Helper for Theorem 14.42: `succHistoryEquivLocal` records the prefix restriction and the final
state. -/
@[simp] private theorem succHistoryEquivLocal_apply
    (m : ℕ) (z : Π _ : Finset.Iic (m + 1), E) :
    succHistoryEquivLocal (E := E) m z =
      (Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ E) (Nat.le_succ m) z,
        z ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩) := by
  -- Route correction: use the same explicit `frestrictLe₂` normal form as the sibling
  -- ordered-history proofs, so later split rewrites become definitional.
  rfl

/-- Helper for Theorem 14.42: splitting the canonical `IicProdIoc` glue map recovers the stored
prefix together with the terminal singleton coordinate. -/
@[simp] private theorem succHistoryEquivLocal_apply_IicProdIoc
    (m : ℕ) (z : (Π _ : Finset.Iic m, E) × (Π _ : Finset.Ioc m (m + 1), E)) :
    succHistoryEquivLocal (E := E) m
        (_root_.IicProdIoc (X := fun _ : ℕ ↦ E) m (m + 1) z) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m).symm z := by
  -- Proof comment: splitting the glued history recovers the prefix restriction and collapses the
  -- singleton tail coordinate back to the final state.
  rcases z with ⟨z₁, z₂⟩
  apply Prod.ext
  · ext i
    have hi : (i : ℕ) ≤ m := Finset.mem_Iic.mp i.2
    simpa [succHistoryEquivLocal_apply, _root_.IicProdIoc_def,
      MeasurableEquiv.piSingleton, hi] using
      congrFun
        (congrFun
          (frestrictLe₂_comp_IicProdIoc (X := fun _ : ℕ ↦ E) (hab := Nat.le_succ m))
          (z₁, z₂))
        i
  · simp [succHistoryEquivLocal_apply, _root_.IicProdIoc_def, MeasurableEquiv.piSingleton]

/-- Helper for Theorem 14.42: package the pointwise `succHistoryEquivLocal` normalization as the
function equality consumed by `Kernel.map_comp_right`. -/
private theorem succHistoryEquivLocal_comp_IicProdIoc
    (m : ℕ) :
    succHistoryEquivLocal (E := E) m ∘
        _root_.IicProdIoc (X := fun _ : ℕ ↦ E) m (m + 1) =
      Prod.map id (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m).symm := by
  -- Proof comment: `succHistoryEquivLocal` first splits the successor history into prefix plus
  -- singleton tail, and then collapses that singleton tail back to the final state.
  funext z
  simpa [Function.comp] using succHistoryEquivLocal_apply_IicProdIoc (E := E) m z

/-- Helper for Theorem 14.42: after splitting a positive-length history into its prefix and final
state, the finite-dimensional law factors as the prefix law composed with the final-step kernel. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {m : ℕ}
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (j : Π _ : Finset.Iic (m + 1), I) (hj : StrictMono j) (x : E) :
    let jPrefix : Π _ : Finset.Iic m, I := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ m))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    let lastPrefix : (Π _ : Finset.Iic m, E) → E := fun z ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩
    let hLastIdx :
        (⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ : Finset.Iic (m + 1)) <
          ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast m
    let hLast :
        j ⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ <
          j ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal (E := E) m) =
      (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
        Kernel.comap (K hLast) lastPrefix (measurable_lastIicCoordinate (E := E) (m := m)) := by
  let jPrefix : Π _ : Finset.Iic m, I := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ m))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let lastPrefix : (Π _ : Finset.Iic m, E) → E := fun z ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ : Finset.Iic (m + 1)) <
        ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast m
  let hLast :
      j ⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ <
        j ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let hlastPrefixMeasurable : Measurable lastPrefix := by
    simpa [lastPrefix] using measurable_lastIicCoordinate (E := E) (m := m)
  let κhist :
      (r : ℕ) → Kernel (Π _ : Finset.Iic r, E) E :=
    consistentFamilyHistoryKernels K j hj
  let stepKernel : Kernel (Π _ : Finset.Iic m, E) E :=
    Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable
  let splitKernel :
      Kernel (Π _ : Finset.Iic m, E) ((Π _ : Finset.Iic m, E) × E) :=
    Kernel.id ×ₖ stepKernel
  have hstepKernel :
      κhist m = stepKernel := by
    -- Proof comment: at the terminal prefix index, the history-extension kernel is exactly the
    -- last-step row read from the last prefix coordinate.
    dsimp [κhist, consistentFamilyHistoryKernels]
    simp [Nat.lt_succ_self, stepKernel, hLast, hLastIdx]
    change Kernel.comap (K hLast) historyLast measurable_historyLast =
      Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable
    rfl
  have hsplitKernel :
      ((ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ E) (κ := κhist) m (m + 1)).map
          (succHistoryEquivLocal (E := E) m) :
            Kernel (Π _ : Finset.Iic m, E) ((Π _ : Finset.Iic m, E) × E)) =
        splitKernel := by
    letI : IsMarkovKernel (K hLast) := hMarkov hLast
    letI : IsSFiniteKernel stepKernel := by
      dsimp [stepKernel]
      infer_instance
    letI :
        IsSFiniteKernel
          ((κhist m).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m)) := by
      simpa [hstepKernel] using
        (inferInstance :
          IsSFiniteKernel
            (stepKernel.map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m)))
    -- Proof comment: the one-step partial trajectory becomes the identity on the stored prefix
    -- paired with the final-step kernel once the successor history is split into `(prefix,last)`.
    rw [ProbabilityTheory.Kernel.partialTraj_succ_self]
    rw [← Kernel.map_comp_right
      (κ := Kernel.id ×ₖ
        ((κhist m).map (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m)))
      (f := _root_.IicProdIoc (X := fun _ : ℕ ↦ E) m (m + 1))
      (g := succHistoryEquivLocal (E := E) m)
      measurable_IicProdIoc
      (succHistoryEquivLocal (E := E) m).measurable]
    rw [succHistoryEquivLocal_comp_IicProdIoc (E := E) m]
    rw [← Kernel.map_prod_map _ _ measurable_id
      (MeasurableEquiv.symm
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m)).measurable]
    rw [Kernel.map_id]
    rw [hstepKernel]
    rw [← Kernel.map_comp_right _
      (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m).measurable
      (MeasurableEquiv.symm
        (MeasurableEquiv.piSingleton (X := fun _ : ℕ ↦ E) m)).measurable]
    simpa [splitKernel] using Kernel.map_id stepKernel
  have hκhistPrefix :
      ∀ r, r < m →
        κhist r = (consistentFamilyHistoryKernels K jPrefix hjPrefix) r := by
    intro r hr
    have hrle : r ≤ m := Nat.le_of_lt hr
    -- Proof comment: before the last time, the history families attached to `j` and `jPrefix`
    -- use exactly the same kernels and last-coordinate map.
    simp [κhist, consistentFamilyHistoryKernels, jPrefix, hr, hrle]
  have hpartialPrefix :
      ∀ r, r ≤ m →
        ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ E) (κ := κhist) 0 r =
          ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ E)
            (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix) 0 r := by
    intro r
    induction r with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hr
        have hk : k < m := Nat.lt_of_succ_le hr
        rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
          (X := fun _ : ℕ ↦ E) (κ := κhist) (Nat.zero_le k)]
        rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
          (X := fun _ : ℕ ↦ E)
          (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix) (Nat.zero_le k)]
        rw [ProbabilityTheory.Kernel.partialTraj_succ_self
          (X := fun _ : ℕ ↦ E) (κ := κhist)]
        rw [ProbabilityTheory.Kernel.partialTraj_succ_self
          (X := fun _ : ℕ ↦ E)
          (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix)]
        rw [hκhistPrefix k hk, ih (Nat.le_of_lt hk)]
  have hsucc :
      consistentFamilyFiniteDimensionalKernel K j hj =
        ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ E) (κ := κhist) m (m + 1) ∘ₖ
          consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix := by
    -- Proof comment: the successor finite-dimensional kernel factors as the prefix-history law
    -- followed by one additional extension step.
    rw [consistentFamilyFiniteDimensionalKernel, consistentFamilyFiniteDimensionalKernel,
      consistentFamilyHistoryTraj, consistentFamilyHistoryTraj]
    change
      ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ E) (κ := κhist) 0 (m + 1) ∘ₖ
        Kernel.deterministic initialHistory measurable_initialHistory =
      ProbabilityTheory.Kernel.partialTraj
          (X := fun _ : ℕ ↦ E) (κ := κhist) m (m + 1) ∘ₖ
        (ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ E)
            (κ := consistentFamilyHistoryKernels K jPrefix hjPrefix) 0 m ∘ₖ
          Kernel.deterministic initialHistory measurable_initialHistory)
    rw [ProbabilityTheory.Kernel.partialTraj_succ_eq_comp
      (X := fun _ : ℕ ↦ E) (κ := κhist) (Nat.zero_le m)]
    rw [Kernel.comp_assoc]
    rw [hpartialPrefix m le_rfl]
  letI : IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov K hMarkov jPrefix hjPrefix
  letI : IsProbabilityMeasure (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) := by
    change IsProbabilityMeasure ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x)
    infer_instance
  -- Proof comment: combine the one-step split of the history kernel with the public factorization
  -- of the finite-dimensional law through the final history extension step.
  calc
    (consistentFamilyFiniteDimensionalKernel K j hj x).map (succHistoryEquivLocal (E := E) m) =
        (((ProbabilityTheory.Kernel.partialTraj
            (X := fun _ : ℕ ↦ E) (κ := κhist) m (m + 1)).map
            (succHistoryEquivLocal (E := E) m)) ∘ₖ
              consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
          rw [hsucc]
          rw [← Kernel.map_apply
            (ProbabilityTheory.Kernel.partialTraj
              (X := fun _ : ℕ ↦ E) (κ := κhist) m (m + 1) ∘ₖ
                consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix)
            (succHistoryEquivLocal (E := E) m).measurable x]
          simpa using congrArg
            (fun ξ :
              Kernel E ((Π _ : Finset.Iic m, E) × E) ↦ ξ x)
            (Kernel.map_comp
              (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix)
              (ProbabilityTheory.Kernel.partialTraj
                (X := fun _ : ℕ ↦ E) (κ := κhist) m (m + 1))
              (succHistoryEquivLocal (E := E) m))
    _ = (splitKernel ∘ₖ consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x := by
          rw [hsplitKernel]
    _ = (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ stepKernel := by
          simpa [splitKernel, stepKernel] using
            (Measure.compProd_eq_comp_prod
              (μ := consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x)
              (κ := stepKernel)).symm

/-- Helper for Theorem 14.42: deleting the terminal coordinate of an ordered chain recovers the
prefix finite-dimensional law. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_prefix
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {m : ℕ}
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (j : Π _ : Finset.Iic (m + 1), I) (hj : StrictMono j) (x : E) :
    let jPrefix : Π _ : Finset.Iic m, I := fun i ↦
      j ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ m))⟩
    let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : Π _ : Finset.Iic (m + 1), E ↦
          Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ E) (Nat.le_succ m) z) =
      (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x :
        Measure (Π _ : Finset.Iic m, E)) := by
  let jPrefix : Π _ : Finset.Iic m, I := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ m))⟩
  let hjPrefix : StrictMono jPrefix := fun i k hik ↦ hj (by simpa using hik)
  let prefixProjection : ((Π _ : Finset.Iic m, E) × E) → Π _ : Finset.Iic m, E := Prod.fst
  let lastPrefix : (Π _ : Finset.Iic m, E) → E := fun z ↦ z ⟨m, Finset.mem_Iic.2 le_rfl⟩
  let hLastIdx :
      (⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ : Finset.Iic (m + 1)) <
        ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := lastIic_lt_succLast m
  let hLast :
      j ⟨m, Finset.mem_Iic.2 (Nat.le_succ m)⟩ <
        j ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := hj hLastIdx
  let hlastPrefixMeasurable : Measurable lastPrefix := by
    fun_prop
  letI : IsMarkovKernel (K hLast) := hMarkov hLast
  letI :
      IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov K hMarkov jPrefix hjPrefix
  letI :
      IsProbabilityMeasure (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) := by
    change IsProbabilityMeasure ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x)
    infer_instance
  have hcomp :
      prefixProjection ∘ succHistoryEquivLocal (E := E) m =
        (fun z : Π _ : Finset.Iic (m + 1), E ↦
          Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ E) (Nat.le_succ m) z) := by
    -- Proof comment: the first coordinate of the split history is exactly the prefix tuple.
    funext z
    simp [prefixProjection, succHistoryEquivLocal_apply]
  -- Proof comment: rewrite the prefix marginal through the split equivalence and then take the
  -- first marginal of the composition-product measure.
  calc
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : Π _ : Finset.Iic (m + 1), E ↦
          Preorder.frestrictLe₂ (π := fun _ : ℕ ↦ E) (Nat.le_succ m) z) =
        (((consistentFamilyFiniteDimensionalKernel K j hj x).map
            (succHistoryEquivLocal (E := E) m)).map prefixProjection) := by
          symm
          rw [Measure.map_map measurable_fst (succHistoryEquivLocal (E := E) m).measurable]
          exact congrArg (fun f ↦ Measure.map f ((consistentFamilyFiniteDimensionalKernel K j hj) x))
            hcomp
    _ =
        (((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
            Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable).map
              prefixProjection) := by
          rw [consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
            (E := E) (K := K) (hMarkov := hMarkov) (j := j) (hj := hj) (x := x)]
    _ =
        ((((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
            Kernel.comap (K hLast) lastPrefix hlastPrefixMeasurable).fst)) := by
          rw [Measure.fst]
    _ = consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x := by
          rw [Measure.fst_compProd]

/-- Helper for Theorem 14.42: `deleteOneIicEmbedding k` is the canonical ordered embedding
omitting the positive coordinate `k.succ`. -/
private noncomputable def deleteOneIicEmbedding (n : ℕ) (k : Fin (n + 1)) :
    Finset.Iic n ↪o Finset.Iic (n + 1) :=
  (((iicOrderIsoFinLocal n).toOrderEmbedding.trans
      (Fin.succAboveOrderEmb k.succ)).trans
    (iicOrderIsoFinLocal (n + 1)).symm.toOrderEmbedding)

/-- Helper for Theorem 14.42: `deleteOneIicEmbedding` is exactly the transported
`Fin.succAbove` map. -/
private theorem deleteOneIicEmbedding_apply
    (n : ℕ) (k : Fin (n + 1)) (i : Finset.Iic n) :
    deleteOneIicEmbedding n k i =
      finToIicLocal (n + 1) (k.succ.succAbove (iicToFinLocal n i)) := by
  rfl

/-- Helper for Theorem 14.42: deleting a positive coordinate still fixes the bottom index. -/
private theorem deleteOneIicEmbedding_zero
    (n : ℕ) (k : Fin (n + 1)) :
    deleteOneIicEmbedding n k ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ =
      ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩ := by
  -- Proof comment: after transporting to `Fin`, the deleted coordinate is positive, so
  -- `succAbove` sends `0` to `0`.
  rw [deleteOneIicEmbedding_apply]
  change finToIicLocal (n + 1) (k.succ.succAbove 0) =
    ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩
  rw [Fin.succ_succAbove_zero]
  rfl

/-- Helper for Theorem 14.42: deleting the last coordinate is exactly the existing prefix
inclusion. -/
private theorem deleteOneIicEmbedding_last_eq_prefix
    (n : ℕ) :
    ∀ i : Finset.Iic n,
      deleteOneIicEmbedding n (Fin.last n) i =
        ⟨i.1, Finset.mem_Iic.2
          (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩ := by
  intro i
  -- Proof comment: deleting the final coordinate is just `Fin.castSucc` transported through the
  -- `Finset.Iic`/`Fin` order isomorphisms.
  cases i with
  | mk val hval =>
      simp [deleteOneIicEmbedding, iicOrderIsoFinLocal, iicToFinLocal, finToIicLocal,
        Fin.succAbove_last]

/-- Helper for Theorem 14.42: after deleting an interior coordinate, splitting the shortened
history is the same as first splitting the long history and then deleting the corresponding
prefix coordinate. -/
private theorem deleteOneIicEmbedding_preserves_last
    {m : ℕ} (k : Fin (m + 1)) :
    deleteOneIicEmbedding (m + 1) k.castSucc ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ =
      ⟨m + 2, Finset.mem_Iic.2 le_rfl⟩ := by
  -- Route correction: the old statement was false for `k = Fin.last m`, because deleting the
  -- terminal positive coordinate does not preserve the last index. The split theorem only needs
  -- the `k.castSucc` interior-deletion case, where the last coordinate is preserved.
  -- Proof comment: after transporting to `Fin`, the deleted coordinate is
  -- `k.castSucc.succ`, which is not the terminal index, so `succAbove` fixes `Fin.last`.
  change finToIicLocal (m + 2) (k.castSucc.succ.succAbove (Fin.last (m + 1))) =
      finToIicLocal (m + 2) (Fin.last (m + 2))
  exact congrArg (finToIicLocal (m + 2))
    (Fin.succAbove_ne_last_last (a := k.castSucc.succ)
      (by
        simpa using
          (Fin.succ_ne_last_iff k.castSucc).2 (Fin.castSucc_ne_last k)))

/-- Helper for Theorem 14.42: on prefix coordinates, deleting `k.castSucc` from the longer chain
agrees with deleting `k` from the shorter chain and then casting that result into the longer
target. -/
private theorem deleteOneIicEmbedding_castSucc_prefix
    {m : ℕ} (k : Fin (m + 1)) (i : Finset.Iic m) :
    deleteOneIicEmbedding (m + 1) k.castSucc
      ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ m))⟩ =
      ⟨(deleteOneIicEmbedding m k i).1, Finset.mem_Iic.2
        (Nat.le_trans
          (Finset.mem_Iic.mp (deleteOneIicEmbedding m k i).2)
          (Nat.le_succ (m + 1)))⟩ := by
  -- Proof comment: after transporting both delete-one maps to `Fin`, the prefix coordinate
  -- identity is exactly `Fin.castSucc_succAbove_castSucc`.
  change
    finToIicLocal (m + 2)
      ((k.castSucc.succ).succAbove ((iicToFinLocal m i).castSucc)) =
      finToIicLocal (m + 2) ((k.succ.succAbove (iicToFinLocal m i)).castSucc)
  congr 1
  rw [Fin.succ_castSucc]
  exact Fin.castSucc_succAbove_castSucc (i := k.succ) (j := iicToFinLocal m i)

/-- Helper for Theorem 14.42: after deleting an interior coordinate, splitting the shortened
history is the same as first splitting the long history and then deleting the corresponding
prefix coordinate. -/
private theorem deleteOneIicEmbedding_split_castSucc
    {m : ℕ} (k : Fin (m + 1)) :
    (fun z : Π _ : Finset.Iic (m + 2), E ↦
      succHistoryEquivLocal (E := E) m
        (fun i : Finset.Iic (m + 1) ↦ z (deleteOneIicEmbedding (m + 1) k.castSucc i))) =
      (fun z : Π _ : Finset.Iic (m + 2), E ↦
        Prod.map
          (fun y : Π _ : Finset.Iic (m + 1), E ↦
            fun i : Finset.Iic m ↦ y (deleteOneIicEmbedding m k i))
          id
          (succHistoryEquivLocal (E := E) (m + 1) z)) := by
  -- Proof comment: compare both split histories componentwise; on prefix coordinates the two
  -- delete-one maps differ only by `Fin.castSucc_succAbove_castSucc`, and the terminal
  -- coordinate is preserved by the previous lemma.
  funext z
  apply Prod.ext
  · ext i
    -- Proof comment: the prefix component is exactly the dedicated cast-stable delete-one
    -- transport from the previous helper.
    rw [succHistoryEquivLocal_apply, succHistoryEquivLocal_apply]
    change
      z (deleteOneIicEmbedding (m + 1) k.castSucc
        ⟨i.1, Finset.mem_Iic.2
          (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ m))⟩) =
        z ⟨(deleteOneIicEmbedding m k i).1, Finset.mem_Iic.2
          (Nat.le_trans
            (Finset.mem_Iic.mp (deleteOneIicEmbedding m k i).2)
            (Nat.le_succ (m + 1)))⟩
    rw [deleteOneIicEmbedding_castSucc_prefix (k := k) (i := i)]
  · -- Proof comment: interior deletion leaves the terminal coordinate untouched.
    rw [succHistoryEquivLocal_apply, succHistoryEquivLocal_apply]
    change z (deleteOneIicEmbedding (m + 1) k.castSucc ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩) =
        z ⟨m + 2, Finset.mem_Iic.2 le_rfl⟩
    rw [deleteOneIicEmbedding_preserves_last (k := k)]

/-- Helper for Theorem 14.42: if the deleted prefix coordinate is not the last prefix index, then
the last prefix coordinate is preserved by `deleteOneIicEmbedding`. -/
private theorem deleteOneIicEmbedding_preserves_prefix_last_of_ne_last
    {m : ℕ} (k : Fin (m + 1)) (hk : k ≠ Fin.last m) :
    deleteOneIicEmbedding m k ⟨m, Finset.mem_Iic.2 le_rfl⟩ =
      ⟨m + 1, Finset.mem_Iic.2 le_rfl⟩ := by
  -- Proof comment: when the deleted prefix coordinate is not the terminal one, the transported
  -- `Fin.succAbove` leaves `Fin.last` unchanged.
  change finToIicLocal (m + 1) (k.succ.succAbove (Fin.last m)) =
      finToIicLocal (m + 1) (Fin.last (m + 1))
  exact congrArg (finToIicLocal (m + 1))
    (Fin.succAbove_ne_last_last (a := k.succ) ((Fin.succ_ne_last_iff k).2 hk))

/-- Helper for Theorem 14.42: the delete-one projection on a split prefix history is measurable. -/
private theorem measurable_deleteOneIicSplitProjection
    {m : ℕ} (k : Fin (m + 1)) :
    Measurable
      (fun y : Π _ : Finset.Iic (m + 1), E ↦
        fun i : Finset.Iic m ↦ y (deleteOneIicEmbedding m k i)) := by
  -- Proof comment: every coordinate of the shortened prefix history is still just evaluation at a
  -- fixed coordinate of the original prefix history.
  refine measurable_pi_lambda _ ?_
  intro i
  exact measurable_pi_apply (deleteOneIicEmbedding m k i)

/-- Helper for Theorem 14.42: after deleting one interior coordinate, pushing the shortened
history law through the split-history equivalence is the same as splitting first and then deleting
the corresponding prefix coordinate. -/
private theorem measure_map_deleteOneIicEmbedding_split_castSucc
    {m : ℕ} (μ : Measure (Π _ : Finset.Iic (m + 2), E)) (k : Fin (m + 1)) :
    (μ.map
        (fun z : Π _ : Finset.Iic (m + 2), E ↦
          fun i : Finset.Iic (m + 1) ↦ z (deleteOneIicEmbedding (m + 1) k.castSucc i))).map
        (succHistoryEquivLocal (E := E) m) =
      μ.map
        (Prod.map
          (fun y : Π _ : Finset.Iic (m + 1), E ↦
            fun i : Finset.Iic m ↦ y (deleteOneIicEmbedding m k i))
          id ∘ succHistoryEquivLocal (E := E) (m + 1)) := by
  -- Proof comment: compose the two left-hand maps, then rewrite the composite by the previously
  -- established split/delete identity.
  rw [Measure.map_map
    (succHistoryEquivLocal (E := E) m).measurable
    (by
      refine measurable_pi_lambda _ ?_
      intro i
      exact measurable_pi_apply (deleteOneIicEmbedding (m + 1) k.castSucc i))]
  congr 1
  funext z
  simpa [Function.comp] using congrFun (deleteOneIicEmbedding_split_castSucc (E := E) k) z

/-- Helper for Theorem 14.42: pointwise equal ordered chains yield the same finite-dimensional
kernel. -/
private theorem consistentFamilyFiniteDimensionalKernel_congr
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    {j j' : Π _ : Finset.Iic n, I} (hj : StrictMono j) (hj' : StrictMono j')
    (hjj' : j = j') (x : E) :
    consistentFamilyFiniteDimensionalKernel K j hj x =
      consistentFamilyFiniteDimensionalKernel K j' hj' x := by
  -- Proof comment: once the chain functions agree, proof irrelevance identifies the two
  -- strict-monotonicity witnesses, so the kernels are definitionally the same.
  subst hjj'
  have hstrict : hj = hj' := Subsingleton.elim _ _
  subst hstrict
  rfl

/-- Helper for Theorem 14.42: the canonical delete-one map at the last coordinate is the already
proved prefix marginal theorem. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_deleteOneLast
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (j : Π _ : Finset.Iic (n + 1), I) (hj : StrictMono j) (x : E) :
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : Π _ : Finset.Iic (n + 1), E ↦
          fun i : Finset.Iic n ↦ z (deleteOneIicEmbedding n (Fin.last n) i)) =
      consistentFamilyFiniteDimensionalKernel K
        (fun i ↦ j (deleteOneIicEmbedding n (Fin.last n) i))
        (hj.comp (deleteOneIicEmbedding n (Fin.last n)).strictMono) x := by
  -- Proof comment: deleting the final coordinate is exactly the canonical prefix restriction, so
  -- the result is the previously proved prefix marginal theorem.
  simpa [deleteOneIicEmbedding_last_eq_prefix] using
    (consistentFamilyFiniteDimensionalKernel_map_prefix
      (E := E) (K := K) (hMarkov := hMarkov) (j := j) (hj := hj) (x := x))

/-- Helper for Theorem 14.42: if a tail kernel only depends on a measurable base map `f`, then
mapping the corresponding comp-product along `Prod.map f id` recovers the comp-product over the
pushed-forward base law. -/
private theorem compProd_map_base_eq_compProd
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ]
    (f : A → B) (hf : Measurable f)
    (κ : Kernel B C) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ Kernel.comap κ f hf).map (Prod.map f id)) =
      μ.map f ⊗ₘ κ := by
  -- Proof comment: first rewrite the comp-product as a kernel composition, then push the base
  -- map through the product kernel and reassemble the pushed-forward comp-product.
  calc
    ((μ ⊗ₘ Kernel.comap κ f hf).map (Prod.map f id)) =
        (Kernel.deterministic (Prod.map f id) (by fun_prop)) ∘ₘ
          (μ ⊗ₘ Kernel.comap κ f hf) := by
            rw [Measure.deterministic_comp_eq_map]
    _ = ((Kernel.deterministic (Prod.map f id) (by fun_prop)) ∘ₖ
          (Kernel.id ×ₖ Kernel.comap κ f hf)) ∘ₘ μ := by
            rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc]
    _ = (((Kernel.id ×ₖ Kernel.comap κ f hf).map (Prod.map f id)) ∘ₘ μ) := by
            rw [Kernel.deterministic_comp_eq_map]
    _ = (((Kernel.id.map f) ×ₖ Kernel.comap κ f hf) ∘ₘ μ) := by
            rw [Kernel.map_prod_eq (κ := Kernel.id) (η := Kernel.comap κ f hf) hf]
    _ = (((Kernel.id.comap f hf) ×ₖ Kernel.comap κ f hf) ∘ₘ μ) := by
            rw [Kernel.id_map hf, Kernel.id_comap hf]
    _ = (((Kernel.id ×ₖ κ).comap f hf) ∘ₘ μ) := by
            rw [Kernel.comap_prod]
    _ = (((Kernel.id ×ₖ κ) ∘ₖ Kernel.deterministic f hf) ∘ₘ μ) := by
            rw [Kernel.comp_deterministic_eq_comap]
    _ = ((Kernel.id ×ₖ κ) ∘ₘ ((Kernel.deterministic f hf) ∘ₘ μ)) := by
            rw [← Measure.comp_assoc]
    _ = ((Kernel.id ×ₖ κ) ∘ₘ μ.map f) := by
            rw [Measure.deterministic_comp_eq_map]
    _ = μ.map f ⊗ₘ κ := by
            rw [Measure.compProd_eq_comp_prod]

/-- Helper for Theorem 14.42: after splitting a two-step chain `(a,b,c)`, forgetting the middle
state turns the iterated comp-product into the comp-product with the composed kernel. -/
private theorem compProd_map_forgetMiddle_eq_compProd_comp
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) [SFinite μ]
    (κ₁ : Kernel A B) [IsSFiniteKernel κ₁]
    (κ₂ : Kernel B C) [IsSFiniteKernel κ₂] :
    (((μ ⊗ₘ κ₁) ⊗ₘ Kernel.prodMkLeft A κ₂).map
        (fun p : (A × B) × C ↦ (p.1.1, p.2))) =
      μ ⊗ₘ (κ₂ ∘ₖ κ₁) := by
  -- Proof comment: reassociate the triple law to `A × (B × C)`, project away the middle state
  -- on the second factor, and identify the resulting kernel with `κ₂ ∘ₖ κ₁`.
  have hforget :
      (fun p : (A × B) × C ↦ (p.1.1, p.2)) =
        Prod.map id Prod.snd ∘ MeasurableEquiv.prodAssoc := by
    funext p
    rfl
  calc
    (((μ ⊗ₘ κ₁) ⊗ₘ Kernel.prodMkLeft A κ₂).map
        (fun p : (A × B) × C ↦ (p.1.1, p.2))) =
        ((((μ ⊗ₘ κ₁) ⊗ₘ Kernel.prodMkLeft A κ₂).map
            MeasurableEquiv.prodAssoc).map (Prod.map id Prod.snd)) := by
              rw [Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
              exact congrArg
                (fun g ↦ Measure.map g (((μ ⊗ₘ κ₁) ⊗ₘ Kernel.prodMkLeft A κ₂))) hforget.symm
    _ = ((μ ⊗ₘ (κ₁ ⊗ₖ Kernel.prodMkLeft A κ₂)).map (Prod.map id Prod.snd)) := by
          rw [Measure.compProd_assoc']
    _ = μ ⊗ₘ Kernel.snd (κ₁ ⊗ₖ Kernel.prodMkLeft A κ₂) := by
          rw [Measure.compProd_eq_comp_prod, Measure.map_comp _ _ (by fun_prop)]
          rw [← Kernel.map_prod_map
            (κ := Kernel.id) (η := κ₁ ⊗ₖ Kernel.prodMkLeft A κ₂) measurable_id measurable_snd]
          rw [Kernel.map_id, Kernel.snd_eq, ← Measure.compProd_eq_comp_prod]
    _ = μ ⊗ₘ (κ₂ ∘ₖ κ₁) := by
          rw [Kernel.comp_eq_snd_compProd]

/-- Helper for Theorem 14.42: a positive missing coordinate in a `Fin (n + 2)` subchain yields a
factorization through one `succAbove`. -/
private theorem factorSubchainThroughDeleteOneFin
    {m n : ℕ} (hmn : m ≤ n)
    (e : Fin (m + 1) ↪o Fin (n + 2)) (hzero : e 0 = 0) :
    ∃ k : Fin (n + 1), ∃ e' : Fin (m + 1) ↪o Fin (n + 1),
      ∀ i, k.succ.succAbove (e' i) = e i := by
  classical
  have hlt : m + 1 < n + 2 := by omega
  have hnotSurj : ¬ Function.Surjective e := by
    intro hsurj
    exact (not_le_of_gt hlt) (Fin.le_of_surjective e hsurj)
  rw [Function.Surjective] at hnotSurj
  push Not at hnotSurj
  rcases hnotSurj with ⟨p, hp⟩
  have hp0 : p ≠ 0 := by
    intro hp0'
    apply hp 0
    simpa [hp0'] using hzero
  let k : Fin (n + 1) := p.pred hp0
  have hk : k.succ = p := Fin.succ_pred p hp0
  let e' : Fin (m + 1) ↪o Fin (n + 1) :=
    { toFun := fun i => Fin.predAbove k (e i)
      inj' := by
        intro i j hij
        have hi' : e i ≠ k.succ := by
          intro hi
          exact hp i (by simpa [hk] using hi)
        have hj' : e j ≠ k.succ := by
          intro hj
          exact hp j (by simpa [hk] using hj)
        apply e.injective
        calc
          e i = k.succ.succAbove (Fin.predAbove k (e i)) := by
            symm
            exact Fin.succ_succAbove_predAbove (p := k) (i := e i) hi'
          _ = k.succ.succAbove (Fin.predAbove k (e j)) := by
            simpa using congrArg (k.succ.succAbove) hij
          _ = e j := Fin.succ_succAbove_predAbove (p := k) (i := e j) hj'
      map_rel_iff' := by
        intro i j
        constructor
        · intro hij
          have hi' : e i ≠ k.succ := by
            intro hi
            exact hp i (by simpa [hk] using hi)
          have hj' : e j ≠ k.succ := by
            intro hj
            exact hp j (by simpa [hk] using hj)
          have hmap :
              k.succ.succAbove (Fin.predAbove k (e i)) ≤
                k.succ.succAbove (Fin.predAbove k (e j)) := by
            exact (Fin.succAboveOrderEmb k.succ).monotone hij
          have h' : e i ≤ e j := by
            simpa [Fin.succ_succAbove_predAbove (p := k) (i := e i) hi',
              Fin.succ_succAbove_predAbove (p := k) (i := e j) hj'] using hmap
          exact e.map_rel_iff.mp h'
        · intro hij
          exact (Fin.predAbove_right_monotone k) (e.map_rel_iff.mpr hij) }
  refine ⟨k, e', ?_⟩
  intro i
  exact Fin.succ_succAbove_predAbove (p := k) (i := e i) (by
    intro hi
    exact hp i (by simpa [hk] using hi))

/-- Helper for Theorem 14.42: every bottom-preserving subchain of `Finset.Iic (n + 1)` factors
through one canonical delete-one embedding. -/
private theorem factorSubchainThroughDeleteOne
    {m n : ℕ} (hmn : m ≤ n)
    (e : Finset.Iic m ↪o Finset.Iic (n + 1))
    (hzero :
      e ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩ =
        ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩) :
    ∃ k : Fin (n + 1), ∃ e' : Finset.Iic m ↪o Finset.Iic n,
      (∀ i, deleteOneIicEmbedding n k (e' i) = e i) ∧
      e' ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩ =
        ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ := by
  let eFin : Fin (m + 1) ↪o Fin (n + 2) :=
    ((iicOrderIsoFinLocal m).symm.toOrderEmbedding.trans e).trans
      (iicOrderIsoFinLocal (n + 1)).toOrderEmbedding
  have hzeroFin : eFin 0 = 0 := by
    -- Proof comment: transporting the bottom-preserving hypothesis through the two order
    -- isomorphisms turns it into the `Fin`-level zero-coordinate condition.
    simpa [eFin, iicOrderIsoFinLocal, finToIicLocal, iicToFinLocal] using
      congrArg (iicToFinLocal (n + 1)) hzero
  rcases factorSubchainThroughDeleteOneFin hmn eFin hzeroFin with ⟨k, eFin', hfactor⟩
  let e' : Finset.Iic m ↪o Finset.Iic n :=
    ((iicOrderIsoFinLocal m).toOrderEmbedding.trans eFin').trans
      (iicOrderIsoFinLocal n).symm.toOrderEmbedding
  have hdelete : ∀ i, deleteOneIicEmbedding n k (e' i) = e i := by
    intro i
    -- Proof comment: after transporting the shortened chain back to `Finset.Iic`, the desired
    -- factorization is exactly the `Fin`-level `succAbove` identity proved above.
    calc
      deleteOneIicEmbedding n k (e' i) =
          finToIicLocal (n + 1) (k.succ.succAbove (eFin' (iicToFinLocal m i))) := by
            rw [deleteOneIicEmbedding_apply]
            change finToIicLocal (n + 1)
                (k.succ.succAbove
                  (iicToFinLocal n (finToIicLocal n (eFin' (iicToFinLocal m i))))) =
              finToIicLocal (n + 1) (k.succ.succAbove (eFin' (iicToFinLocal m i)))
            rw [finToIicLocal_rightInv n]
      _ = finToIicLocal (n + 1) (eFin (iicToFinLocal m i)) := by
            exact congrArg (finToIicLocal (n + 1)) (hfactor (iicToFinLocal m i))
      _ = e i := by
            rw [show finToIicLocal (n + 1) (eFin (iicToFinLocal m i)) =
                finToIicLocal (n + 1)
                  (iicToFinLocal (n + 1) (e (finToIicLocal m (iicToFinLocal m i)))) by
                  rfl]
            rw [finToIicLocal_leftInv (n + 1), finToIicLocal_leftInv m]
  refine ⟨k, e', hdelete, ?_⟩
  apply (deleteOneIicEmbedding n k).injective
  -- Proof comment: both images of the bottom index agree with the preserved bottom point in the
  -- larger chain, so injectivity of `deleteOneIicEmbedding` recovers the shortened bottom point.
  calc
    deleteOneIicEmbedding n k (e' ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩) =
        e ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩ := hdelete _
    _ = ⟨0, Finset.mem_Iic.2 (Nat.zero_le (n + 1))⟩ := hzero
    _ = deleteOneIicEmbedding n k ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ := by
      symm
      exact deleteOneIicEmbedding_zero n k

/-- Helper for Theorem 14.42: an order embedding of a finite initial segment into itself is the
identity. -/
private theorem orderEmbedding_iic_eq_id {n : ℕ} (e : Finset.Iic n ↪o Finset.Iic n) :
    (e : Finset.Iic n → Finset.Iic n) = id := by
  funext i
  -- Proof comment: strict monotonicity on the finite chain forces both `e i ≤ i` and `i ≤ e i`,
  -- hence every coordinate is fixed.
  exact le_antisymm (StrictMono.apply_le e.strictMono) (StrictMono.le_apply e.strictMono)

/-- Helper for Theorem 14.42: after splitting a history of length `n + 2`, deleting the
penultimate coordinate is the same as splitting the prefix once more and forgetting the middle
state. -/
private theorem deleteLastAfterSuccHistory_eq_forgetMiddle
    {n : ℕ} :
    let deletePrefix :
        (Π _ : Finset.Iic (n + 1), E) → Π _ : Finset.Iic n, E :=
      fun y i ↦ y (deleteOneIicEmbedding n (Fin.last n) i)
    Prod.map deletePrefix id ∘ succHistoryEquivLocal (E := E) (n + 1) =
      (fun p : ((Π _ : Finset.Iic n, E) × E) × E ↦ (p.1.1, p.2)) ∘
        Prod.map (succHistoryEquivLocal (E := E) n) id ∘
          succHistoryEquivLocal (E := E) (n + 1) := by
  let deletePrefix :
      (Π _ : Finset.Iic (n + 1), E) → Π _ : Finset.Iic n, E :=
    fun y i ↦ y (deleteOneIicEmbedding n (Fin.last n) i)
  -- Proof comment: compare the two descriptions after evaluating the stored prefix and final
  -- coordinates componentwise.
  funext z
  apply Prod.ext
  · ext i
    simp [deletePrefix, succHistoryEquivLocal_apply, deleteOneIicEmbedding_last_eq_prefix]
  · simp [succHistoryEquivLocal_apply]

/-- Helper for Theorem 14.42: deleting a nonterminal positive coordinate and then taking the split
prefix chain agrees with first taking the original split prefix chain and then deleting that
prefix coordinate. -/
private theorem deleteOneInteriorPrefixChain_eq
    {n : ℕ} (j : Π _ : Finset.Iic (n + 2), I) (k : Fin (n + 1)) :
    (fun i : Finset.Iic n ↦
      j (deleteOneIicEmbedding (n + 1) k.castSucc
        ⟨i.1, Finset.mem_Iic.2
          (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩)) =
      (fun i : Finset.Iic n ↦
        j ⟨(deleteOneIicEmbedding n k i).1, Finset.mem_Iic.2
          (Nat.le_trans
            (Finset.mem_Iic.mp (deleteOneIicEmbedding n k i).2)
            (Nat.le_succ (n + 1)))⟩) := by
  -- Proof comment: this is exactly the cast-stable delete-one identity from the prefix-transport
  -- helper, repackaged as equality of chain functions.
  funext i
  exact congrArg j (deleteOneIicEmbedding_castSucc_prefix (k := k) (i := i))

/-- Helper for Theorem 14.42: the last-step kernel in the interior delete-one split law is the
direct tail kernel from the original chain. -/
private theorem deleteOneInteriorTailKernel_eq
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic (n + 2), I) (hj : StrictMono j)
    (k : Fin (n + 1)) (hk : k ≠ Fin.last n) :
    let jDelete : Π _ : Finset.Iic (n + 1), I := fun i ↦
      j (deleteOneIicEmbedding (n + 1) k.castSucc i)
    let hDelete :
        jDelete ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ <
          jDelete ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ :=
      hj.comp (deleteOneIicEmbedding (n + 1) k.castSucc).strictMono (lastIic_lt_succLast n)
    let hLast :
        j ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ <
          j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ :=
      hj (show
        (⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ : Finset.Iic (n + 2)) <
          ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ by
            simpa using Nat.lt_succ_self (n + 1))
    Kernel.comap
        (K hDelete)
        (fun z : Π _ : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (measurable_lastIicCoordinate (E := E) (m := n)) =
      Kernel.comap
        (K hLast)
        (fun z : Π _ : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
        (measurable_lastIicCoordinate (E := E) (m := n)) := by
  intro jDelete hDelete hLast
  -- Proof comment: the deleted chain keeps the last prefix state and the terminal state, so the
  -- final-step inequality for `jDelete` is exactly the original direct tail inequality.
  have hDeleteLeft :
      jDelete ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ =
        j ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ := by
    dsimp [jDelete]
    rw [deleteOneIicEmbedding_castSucc_prefix
      (k := k) (i := ⟨n, Finset.mem_Iic.2 le_rfl⟩)]
    rw [deleteOneIicEmbedding_preserves_prefix_last_of_ne_last (k := k) hk]
  have hDeleteRight :
      jDelete ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ =
        j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ := by
    dsimp [jDelete]
    rw [deleteOneIicEmbedding_preserves_last (k := k)]
  have hDelete' :
      j ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ <
        j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ := by
    rw [← hDeleteLeft, ← hDeleteRight]
    exact hDelete
  have hStep : hDelete' = hLast := by
    apply Subsingleton.elim
  ext y s hs
  have hTerm :
      (K hDelete') (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) s =
        (K hLast) (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) s := by
    simpa using congrArg
      (fun hlt ↦ K hlt (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) s) hStep
  rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E) (m := n)) y s]
  rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E) (m := n)) y s]
  convert hTerm using 1
  simp [hDeleteLeft, hDeleteRight]

/-- Helper for Theorem 14.42: deleting the penultimate time reduces the last two transition
steps to their Chapman--Kolmogorov composite. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_deletePenultimate [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K)
    (x : E) {n : ℕ}
    (j : Π _ : Finset.Iic (n + 2), I) (hj : StrictMono j) :
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : Π _ : Finset.Iic (n + 2), E ↦
          fun i : Finset.Iic (n + 1) ↦
            z (deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc i)) =
      consistentFamilyFiniteDimensionalKernel K
        (fun i ↦ j (deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc i))
        (hj.comp (deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc).strictMono) x := by
  let deleteProjection :
      (Π _ : Finset.Iic (n + 2), E) → Π _ : Finset.Iic (n + 1), E :=
    fun z i ↦ z (deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc i)
  let deletePrefix :
      (Π _ : Finset.Iic (n + 1), E) → Π _ : Finset.Iic n, E :=
    fun y i ↦ y (deleteOneIicEmbedding n (Fin.last n) i)
  let eLong := succHistoryEquivLocal (E := E) (n + 1)
  let eShort := succHistoryEquivLocal (E := E) n
  let splitLong : (Π _ : Finset.Iic (n + 2), E) → (Π _ : Finset.Iic (n + 1), E) × E :=
    eLong
  let splitShort : (Π _ : Finset.Iic (n + 1), E) → (Π _ : Finset.Iic n, E) × E :=
    eShort
  let forgetMiddle : ((Π _ : Finset.Iic n, E) × E) × E → (Π _ : Finset.Iic n, E) × E :=
    fun p ↦ (p.1.1, p.2)
  let jPrefixLong : Π _ : Finset.Iic (n + 1), I := fun i ↦
    j ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ (n + 1)))⟩
  let hjPrefixLong : StrictMono jPrefixLong := fun i i' hii' ↦ hj (by simpa using hii')
  let jPrefixShort : Π _ : Finset.Iic n, I := fun i ↦
    jPrefixLong ⟨i.1, Finset.mem_Iic.2
      (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
  let hjPrefixShort : StrictMono jPrefixShort :=
    fun i i' hii' ↦ hjPrefixLong (by simpa using hii')
  let jDelete : Π _ : Finset.Iic (n + 1), I := fun i ↦
    j (deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc i)
  let hjDelete : StrictMono jDelete :=
    hj.comp (deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc).strictMono
  let lastPrefixShort : (Π _ : Finset.Iic n, E) → E := fun z ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩
  let hStep1 :
      j ⟨n, Finset.mem_Iic.2 (by omega)⟩ <
        j ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ :=
    hj (show
      (⟨n, Finset.mem_Iic.2 (by omega)⟩ : Finset.Iic (n + 2)) <
        ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ by
          simpa using Nat.lt_succ_self n)
  let hStep2 :
      j ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ <
        j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ :=
    hj (show
      (⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ : Finset.Iic (n + 2)) <
        ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ by
          simpa using Nat.lt_succ_self (n + 1))
  let hDirect :
      j ⟨n, Finset.mem_Iic.2 (by omega)⟩ <
        j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ := hStep1.trans hStep2
  let κ1 : Kernel (Π _ : Finset.Iic n, E) E :=
    Kernel.comap (K hStep1) lastPrefixShort (measurable_lastIicCoordinate (E := E) (m := n))
  let κDirect : Kernel (Π _ : Finset.Iic n, E) E :=
    Kernel.comap (K hDirect) lastPrefixShort (measurable_lastIicCoordinate (E := E) (m := n))
  let tailLong : Kernel (Π _ : Finset.Iic (n + 1), E) E :=
    Kernel.comap
      (K hStep2)
      (fun z : Π _ : Finset.Iic (n + 1), E ↦ z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
      (measurable_lastIicCoordinate (E := E) (m := n + 1))
  let tailSplit : Kernel ((Π _ : Finset.Iic n, E) × E) E :=
    Kernel.prodMkLeft (Π _ : Finset.Iic n, E) (K hStep2)
  letI : IsMarkovKernel (K hStep1) := hMarkov hStep1
  letI : IsMarkovKernel (K hStep2) := hMarkov hStep2
  letI :
      IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov K hMarkov jPrefixLong hjPrefixLong
  letI :
      IsProbabilityMeasure (consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong x) := by
    change IsProbabilityMeasure
      ((consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong) x)
    infer_instance
  letI :
      IsMarkovKernel (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov K hMarkov jPrefixShort hjPrefixShort
  letI :
      IsProbabilityMeasure
        (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) := by
    change IsProbabilityMeasure
      ((consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort) x)
    infer_instance
  letI : IsSFiniteKernel κ1 := by
    dsimp [κ1]
    infer_instance
  letI : IsSFiniteKernel tailSplit := by
    dsimp [tailSplit]
    infer_instance
  have hforgetFn :
      Prod.map deletePrefix id ∘ splitLong =
        forgetMiddle ∘ Prod.map splitShort id ∘ splitLong := by
    -- Proof comment: deleting the penultimate coordinate after the first split is exactly the
    -- same as splitting once more and then forgetting the middle state.
    simpa [deletePrefix, splitLong, splitShort, forgetMiddle] using
      (deleteLastAfterSuccHistory_eq_forgetMiddle (E := E) (n := n))
  have htailLong :
      tailLong = Kernel.comap tailSplit splitShort eShort.measurable := by
    -- Proof comment: after the second split, the final transition only sees the newly exposed
    -- terminal state.
    ext y s hs
    rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E) (m := n + 1)) y s]
    rw [Kernel.comap_apply' _ eShort.measurable y s]
    simp [tailLong, tailSplit, eShort, splitShort, succHistoryEquivLocal_apply]
  have hsplitPrefix :
      (consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong x).map splitShort =
        (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ κ1 := by
    -- Proof comment: the prefix of the long split law is itself a one-step split law.
    simpa [jPrefixLong, jPrefixShort, splitShort, κ1] using
      (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
        (E := E) (K := K) (hMarkov := hMarkov) (j := jPrefixLong)
        (hj := hjPrefixLong) (x := x))
  have hcollapse :
      K hStep2 ∘ₖ κ1 = κDirect := by
    have hκ1 :
        κ1 =
          K hStep1 ∘ₖ
            Kernel.deterministic
              lastPrefixShort (measurable_lastIicCoordinate (E := E) (m := n)) := by
      rw [Kernel.comp_deterministic_eq_comap]
    -- Proof comment: the last two transition kernels collapse to the direct step by the
    -- Chapman-Kolmogorov consistency hypothesis.
    calc
      K hStep2 ∘ₖ κ1 =
          K hStep2 ∘ₖ
            (K hStep1 ∘ₖ
              Kernel.deterministic
                lastPrefixShort (measurable_lastIicCoordinate (E := E) (m := n))) := by
              rw [hκ1]
      _ =
          (K hStep2 ∘ₖ K hStep1) ∘ₖ
            Kernel.deterministic
              lastPrefixShort (measurable_lastIicCoordinate (E := E) (m := n)) := by
              rw [Kernel.comp_assoc]
      _ =
          K hDirect ∘ₖ
            Kernel.deterministic
              lastPrefixShort (measurable_lastIicCoordinate (E := E) (m := n)) := by
              rw [hConsistent.comp_eq hStep1 hStep2]
      _ = κDirect := by
              rw [Kernel.comp_deterministic_eq_comap]
  have hsplitDelete :
      (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map splitShort =
        (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ κDirect := by
    let jDeletePrefix : Π _ : Finset.Iic n, I := fun i ↦
      jDelete ⟨i.1, Finset.mem_Iic.2
        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
    let hjDeletePrefix : StrictMono jDeletePrefix :=
      fun i i' hii' ↦ hjDelete (by simpa using hii')
    have hDeletePrefixChain : jDeletePrefix = jPrefixShort := by
      -- Proof comment: deleting the penultimate coordinate leaves the shorter prefix chain
      -- untouched.
      funext i
      apply congrArg j
      calc
        deleteOneIicEmbedding (n + 1) (Fin.last n).castSucc
            ⟨i.1, Finset.mem_Iic.2
              (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩ =
          ⟨(deleteOneIicEmbedding n (Fin.last n) i).1, Finset.mem_Iic.2
            (Nat.le_trans
              (Finset.mem_Iic.mp (deleteOneIicEmbedding n (Fin.last n) i).2)
              (Nat.le_succ (n + 1)))⟩ := by
                exact deleteOneIicEmbedding_castSucc_prefix (k := Fin.last n) (i := i)
        _ = ⟨i.1, Finset.mem_Iic.2
              (Nat.le_trans
                (Finset.mem_Iic.mp i.2)
                (Nat.le_trans (Nat.le_succ n) (Nat.le_succ (n + 1))))⟩ := by
                simp [deleteOneIicEmbedding_last_eq_prefix]
    have hDeleteBase :
        consistentFamilyFiniteDimensionalKernel K jDeletePrefix hjDeletePrefix x =
          consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x := by
      exact consistentFamilyFiniteDimensionalKernel_congr
        (K := K) (hj := hjDeletePrefix) (hj' := hjPrefixShort)
        (hjj' := hDeletePrefixChain) (x := x)
    have hDeleteTail :
        Kernel.comap
            (K (hjDelete (lastIic_lt_succLast n)))
            (fun z : Π _ : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
            (measurable_lastIicCoordinate (E := E) (m := n)) =
          κDirect := by
      have hDeleteLeft :
          jDelete ⟨n, Finset.mem_Iic.2 (Nat.le_succ n)⟩ =
            j ⟨n, Finset.mem_Iic.2 (by omega)⟩ := by
        dsimp [jDelete]
        rw [deleteOneIicEmbedding_castSucc_prefix
          (k := Fin.last n) (i := ⟨n, Finset.mem_Iic.2 le_rfl⟩)]
        simpa [deleteOneIicEmbedding_last_eq_prefix]
      have hDeleteRight :
          jDelete ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩ =
            j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ := by
        dsimp [jDelete]
        rw [deleteOneIicEmbedding_preserves_last (k := Fin.last n)]
      have hDelete' :
          j ⟨n, Finset.mem_Iic.2 (by omega)⟩ <
            j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ := by
        rw [← hDeleteLeft, ← hDeleteRight]
        exact hjDelete (lastIic_lt_succLast n)
      have hStep : hDelete' = hDirect := by
        apply Subsingleton.elim
      ext y s hs
      have hTerm :
          (K hDelete') (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) s =
            (K hDirect) (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) s := by
        simpa using congrArg
          (fun hlt ↦ K hlt (y ⟨n, Finset.mem_Iic.2 le_rfl⟩) s) hStep
      rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E) (m := n)) y s]
      rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E) (m := n)) y s]
      convert hTerm using 1
      simp [κDirect, hDeleteLeft, hDeleteRight]
    -- Proof comment: the deleted chain has the same split prefix law and the direct tail step.
    calc
      (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map splitShort =
          (consistentFamilyFiniteDimensionalKernel K
              jDeletePrefix hjDeletePrefix x) ⊗ₘ
            Kernel.comap
              (K (hjDelete (lastIic_lt_succLast n)))
              (fun z : Π _ : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
              (measurable_lastIicCoordinate (E := E) (m := n)) := by
                simpa [jDeletePrefix, hjDeletePrefix, splitShort] using
                  (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                    (E := E) (K := K) (hMarkov := hMarkov) (j := jDelete)
                    (hj := hjDelete) (x := x))
      _ =
          (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ
            Kernel.comap
              (K (hjDelete (lastIic_lt_succLast n)))
              (fun z : Π _ : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
              (measurable_lastIicCoordinate (E := E) (m := n)) := by
                rw [hDeleteBase]
      _ =
          (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ κDirect := by
                rw [hDeleteTail]
  have hmapSplit : Measurable (Prod.map splitShort (id : E → E)) := by
    exact Measurable.prod (eShort.measurable.comp measurable_fst) measurable_snd
  -- Proof comment: compare both measures after the split equivalence on the shortened chain,
  -- rewrite the long side into a triple comp-product, and collapse the middle state.
  rw [← eShort.map_measurableEquiv_injective.eq_iff]
  calc
    ((consistentFamilyFiniteDimensionalKernel K j hj x).map deleteProjection).map splitShort =
        (consistentFamilyFiniteDimensionalKernel K j hj x).map
          (Prod.map deletePrefix id ∘ splitLong) := by
            simpa [deleteProjection, deletePrefix, splitLong, splitShort] using
              (measure_map_deleteOneIicEmbedding_split_castSucc
                (E := E) (μ := consistentFamilyFiniteDimensionalKernel K j hj x) (Fin.last n))
    _ =
        (consistentFamilyFiniteDimensionalKernel K j hj x).map
          (forgetMiddle ∘ Prod.map splitShort id ∘ splitLong) := by
            rw [hforgetFn]
    _ =
        (((consistentFamilyFiniteDimensionalKernel K j hj x).map splitLong).map
          (Prod.map splitShort id)).map forgetMiddle := by
            rw [← Measure.map_map (by fun_prop)]
            · simpa [splitLong] using
                congrArg (Measure.map forgetMiddle)
                  (Measure.map_map hmapSplit eLong.measurable).symm
            · simpa [splitLong] using hmapSplit.comp eLong.measurable
    _ =
        ((((consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong x) ⊗ₘ tailLong).map
            (Prod.map splitShort id)).map forgetMiddle) := by
              rw [consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                (E := E) (K := K) (hMarkov := hMarkov) (j := j) (hj := hj) (x := x)]
    _ =
        ((((consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong x) ⊗ₘ
            Kernel.comap tailSplit splitShort eShort.measurable).map
              (Prod.map splitShort id)).map forgetMiddle) := by
              rw [htailLong]
    _ =
        ((((consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong x).map splitShort) ⊗ₘ
            tailSplit).map forgetMiddle) := by
              exact congrArg (fun ν : Measure (((Π _ : Finset.Iic n, E) × E) × E) ↦
                ν.map forgetMiddle)
                (compProd_map_base_eq_compProd
                  (μ := consistentFamilyFiniteDimensionalKernel K jPrefixLong hjPrefixLong x)
                  (f := splitShort) (hf := eShort.measurable) (κ := tailSplit))
    _ =
        ((((consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ κ1) ⊗ₘ
            tailSplit).map forgetMiddle) := by
              rw [hsplitPrefix]
    _ =
        (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ
          (K hStep2 ∘ₖ κ1) := by
            rw [compProd_map_forgetMiddle_eq_compProd_comp]
    _ =
        (consistentFamilyFiniteDimensionalKernel K jPrefixShort hjPrefixShort x) ⊗ₘ κDirect := by
            rw [hcollapse]
    _ = (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map splitShort := by
            symm
            exact hsplitDelete

/-- Helper for Theorem 14.42: deleting one positive coordinate should be the unique
Chapman--Kolmogorov step still missing after the terminal prefix case. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_deleteOneCanonical [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K)
    (x : E) {n : ℕ}
    (j : Π _ : Finset.Iic (n + 1), I) (hj : StrictMono j) (k : Fin (n + 1)) :
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : Π _ : Finset.Iic (n + 1), E ↦
          fun i : Finset.Iic n ↦ z (deleteOneIicEmbedding n k i)) =
      consistentFamilyFiniteDimensionalKernel K
        (fun i ↦ j (deleteOneIicEmbedding n k i))
        (hj.comp (deleteOneIicEmbedding n k).strictMono) x := by
  induction n with
  | zero =>
      -- Proof comment: with only one positive coordinate, delete-one is exactly the terminal
      -- prefix projection already handled by the sibling theorem.
      have hk : k = 0 := Fin.eq_zero k
      subst hk
      simpa using
        (consistentFamilyFiniteDimensionalKernel_map_deleteOneLast
          (E := E) (K := K) (hMarkov := hMarkov) (j := j) (hj := hj) (x := x))
  | succ n ih =>
      cases k using Fin.lastCases with
      | last =>
          -- Proof comment: deleting the final positive coordinate is again the existing prefix
          -- marginal theorem.
          simpa using
            (consistentFamilyFiniteDimensionalKernel_map_deleteOneLast
              (E := E) (K := K) (hMarkov := hMarkov) (j := j) (hj := hj) (x := x))
      | cast k =>
          let deleteProjection :
              (Π _ : Finset.Iic (n + 2), E) → Π _ : Finset.Iic (n + 1), E :=
            fun z i ↦ z (deleteOneIicEmbedding (n + 1) k.castSucc i)
          let deletePrefix :
              (Π _ : Finset.Iic (n + 1), E) → Π _ : Finset.Iic n, E :=
            fun y i ↦ y (deleteOneIicEmbedding n k i)
          let jDelete : Π _ : Finset.Iic (n + 1), I := fun i ↦
            j (deleteOneIicEmbedding (n + 1) k.castSucc i)
          let hjDelete : StrictMono jDelete :=
            hj.comp (deleteOneIicEmbedding (n + 1) k.castSucc).strictMono
          have hdeleteProjection :
              Measurable deleteProjection := by
            refine measurable_pi_lambda _ ?_
            intro i
            exact measurable_pi_apply (deleteOneIicEmbedding (n + 1) k.castSucc i)
          have hdeletePrefix :
              Measurable deletePrefix := by
            exact measurable_deleteOneIicSplitProjection (E := E) k
          -- Proof comment: compare the two measures after splitting the shortened history into
          -- prefix plus terminal state; the easy terminal branches are already closed above.
          apply (succHistoryEquivLocal (E := E) n).map_measurableEquiv_injective
          calc
            ((consistentFamilyFiniteDimensionalKernel K j hj x).map deleteProjection).map
                (succHistoryEquivLocal (E := E) n) =
              (consistentFamilyFiniteDimensionalKernel K j hj x).map
                (Prod.map deletePrefix id ∘ succHistoryEquivLocal (E := E) (n + 1)) := by
                  simpa [deleteProjection, deletePrefix] using
                    (measure_map_deleteOneIicEmbedding_split_castSucc
                      (E := E) (μ := consistentFamilyFiniteDimensionalKernel K j hj x) k)
            _ =
              (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map
                (succHistoryEquivLocal (E := E) n) := by
                  by_cases hkLast : k = Fin.last n
                  · subst hkLast
                    calc
                      (consistentFamilyFiniteDimensionalKernel K j hj x).map
                          (Prod.map deletePrefix id ∘
                            succHistoryEquivLocal (E := E) (n + 1)) =
                          ((consistentFamilyFiniteDimensionalKernel K j hj x).map
                              deleteProjection).map
                            (succHistoryEquivLocal (E := E) n) := by
                              symm
                              simpa [deleteProjection, deletePrefix] using
                                (measure_map_deleteOneIicEmbedding_split_castSucc
                                  (E := E)
                                  (μ := consistentFamilyFiniteDimensionalKernel K j hj x)
                                  (Fin.last n))
                      _ =
                          (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map
                            (succHistoryEquivLocal (E := E) n) := by
                              exact congrArg
                                (fun ν : Measure (Π _ : Finset.Iic (n + 1), E) ↦
                                  ν.map (succHistoryEquivLocal (E := E) n))
                                (consistentFamilyFiniteDimensionalKernel_map_deletePenultimate
                                  (I := I) (E := E) (K := K) (hMarkov := hMarkov)
                                  (hConsistent := hConsistent) (x := x) (j := j) (hj := hj))
                  · let jPrefix : Π _ : Finset.Iic (n + 1), I := fun i ↦
                      j ⟨i.1, Finset.mem_Iic.2
                        (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ (n + 1)))⟩
                    let hjPrefix : StrictMono jPrefix :=
                      fun i i' hii' ↦ hj (by simpa using hii')
                    let hLast :
                        j ⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ <
                          j ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ :=
                      hj (show
                        (⟨n + 1, Finset.mem_Iic.2 (by omega)⟩ : Finset.Iic (n + 2)) <
                          ⟨n + 2, Finset.mem_Iic.2 le_rfl⟩ by
                            simpa using Nat.lt_succ_self (n + 1))
                    let tailShort : Kernel (Π _ : Finset.Iic n, E) E :=
                      Kernel.comap (K hLast)
                        (fun z : Π _ : Finset.Iic n, E ↦ z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                        (measurable_lastIicCoordinate (E := E) (m := n))
                    letI : IsMarkovKernel (K hLast) := hMarkov hLast
                    letI : IsSFiniteKernel tailShort := by
                      dsimp [tailShort]
                      infer_instance
                    letI : IsMarkovKernel
                        (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) :=
                      consistentFamilyFiniteDimensionalKernel_isMarkov K hMarkov jPrefix hjPrefix
                    letI :
                        IsProbabilityMeasure
                          (consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) := by
                      change IsProbabilityMeasure
                        ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix) x)
                      infer_instance
                    have htail :
                        Kernel.comap
                            (K hLast)
                            (fun z : Π _ : Finset.Iic (n + 1), E ↦
                              z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
                            (measurable_lastIicCoordinate (E := E) (m := n + 1)) =
                          Kernel.comap tailShort deletePrefix hdeletePrefix := by
                            ext y s hs
                            rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E)
                              (m := n + 1)) y s]
                            rw [Kernel.comap_apply' _ hdeletePrefix y s]
                            rw [Kernel.comap_apply' _ (measurable_lastIicCoordinate (E := E)
                              (m := n)) (deletePrefix y) s]
                            simp [deletePrefix,
                              deleteOneIicEmbedding_preserves_prefix_last_of_ne_last
                                (k := k) hkLast]
                    have hsplitDelete :
                        (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map
                            (succHistoryEquivLocal (E := E) n) =
                          (consistentFamilyFiniteDimensionalKernel K
                              (fun i ↦ jPrefix (deleteOneIicEmbedding n k i))
                              (hjPrefix.comp (deleteOneIicEmbedding n k).strictMono) x) ⊗ₘ
                            tailShort := by
                              let jDeletePrefix : Π _ : Finset.Iic n, I := fun i ↦
                                jDelete ⟨i.1, Finset.mem_Iic.2
                                  (Nat.le_trans (Finset.mem_Iic.mp i.2) (Nat.le_succ n))⟩
                              let hjDeletePrefix : StrictMono jDeletePrefix :=
                                fun i i' hii' ↦ hjDelete (by simpa using hii')
                              have hPrefixChain :
                                  jDeletePrefix =
                                    fun i : Finset.Iic n ↦ jPrefix (deleteOneIicEmbedding n k i) := by
                                -- Proof comment: deleting an interior coordinate commutes with
                                -- the split-prefix reindexing on the chain level.
                                funext i
                                simpa [jDelete, jPrefix] using
                                  congrFun
                                    (deleteOneInteriorPrefixChain_eq
                                      (j := j) (k := k)) i
                              have hBase :
                                  consistentFamilyFiniteDimensionalKernel K
                                      jDeletePrefix hjDeletePrefix x =
                                    consistentFamilyFiniteDimensionalKernel K
                                      (fun i ↦ jPrefix (deleteOneIicEmbedding n k i))
                                      (hjPrefix.comp (deleteOneIicEmbedding n k).strictMono) x := by
                                -- Proof comment: the split-prefix finite-dimensional laws agree
                                -- once the prefix chains are identified.
                                exact consistentFamilyFiniteDimensionalKernel_congr
                                  (K := K) (hj := hjDeletePrefix)
                                  (hj' := hjPrefix.comp (deleteOneIicEmbedding n k).strictMono)
                                  (hjj' := hPrefixChain) (x := x)
                              have hTail :
                                  Kernel.comap
                                      (K (hjDelete (lastIic_lt_succLast n)))
                                      (fun z : Π _ : Finset.Iic n, E ↦
                                        z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                                      (measurable_lastIicCoordinate (E := E) (m := n)) =
                                    tailShort := by
                                -- Proof comment: the final step of the deleted chain is the
                                -- original direct tail step.
                                simpa [tailShort] using
                                  (deleteOneInteriorTailKernel_eq
                                    (E := E) (K := K) (j := j) (hj := hj)
                                    (k := k) hkLast)
                              -- Proof comment: apply the split theorem to `jDelete` and rewrite
                              -- the prefix chain and tail kernel independently.
                              calc
                                (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map
                                    (succHistoryEquivLocal (E := E) n) =
                                  (consistentFamilyFiniteDimensionalKernel K
                                      jDeletePrefix hjDeletePrefix x) ⊗ₘ
                                    Kernel.comap
                                      (K (hjDelete (lastIic_lt_succLast n)))
                                      (fun z : Π _ : Finset.Iic n, E ↦
                                        z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                                      (measurable_lastIicCoordinate (E := E) (m := n)) := by
                                        simpa [jDeletePrefix, hjDeletePrefix] using
                                          (consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                                            (E := E) (K := K) (hMarkov := hMarkov) (j := jDelete)
                                            (hj := hjDelete) (x := x))
                                _ =
                                  (consistentFamilyFiniteDimensionalKernel K
                                      (fun i ↦ jPrefix (deleteOneIicEmbedding n k i))
                                      (hjPrefix.comp (deleteOneIicEmbedding n k).strictMono) x) ⊗ₘ
                                    Kernel.comap
                                      (K (hjDelete (lastIic_lt_succLast n)))
                                      (fun z : Π _ : Finset.Iic n, E ↦
                                        z ⟨n, Finset.mem_Iic.2 le_rfl⟩)
                                      (measurable_lastIicCoordinate (E := E) (m := n)) := by
                                        rw [hBase]
                                _ =
                                  (consistentFamilyFiniteDimensionalKernel K
                                      (fun i ↦ jPrefix (deleteOneIicEmbedding n k i))
                                      (hjPrefix.comp (deleteOneIicEmbedding n k).strictMono) x) ⊗ₘ
                                    tailShort := by
                                        rw [hTail]
                    calc
                      (consistentFamilyFiniteDimensionalKernel K j hj x).map
                          (Prod.map deletePrefix id ∘
                            succHistoryEquivLocal (E := E) (n + 1)) =
                          (((consistentFamilyFiniteDimensionalKernel K j hj x).map
                              (succHistoryEquivLocal (E := E) (n + 1))).map
                                (Prod.map deletePrefix id)) := by
                                  symm
                                  rw [Measure.map_map (by fun_prop)
                                    (succHistoryEquivLocal (E := E) (n + 1)).measurable]
                      _ =
                          (((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
                              Kernel.comap
                                (K hLast)
                                (fun z : Π _ : Finset.Iic (n + 1), E ↦
                                  z ⟨n + 1, Finset.mem_Iic.2 le_rfl⟩)
                                (measurable_lastIicCoordinate (E := E) (m := n + 1))).map
                                  (Prod.map deletePrefix id)) := by
                                    rw [consistentFamilyFiniteDimensionalKernel_map_succHistoryEquiv_eq_compProd
                                      (E := E) (K := K) (hMarkov := hMarkov) (j := j)
                                      (hj := hj) (x := x)]
                      _ =
                          (((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x) ⊗ₘ
                              Kernel.comap tailShort deletePrefix hdeletePrefix).map
                                (Prod.map deletePrefix id)) := by
                                  rw [htail]
                      _ =
                          ((consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x).map
                              deletePrefix) ⊗ₘ tailShort := by
                                rw [compProd_map_base_eq_compProd
                                  (μ := consistentFamilyFiniteDimensionalKernel K jPrefix hjPrefix x)
                                  (f := deletePrefix) (hf := hdeletePrefix) (κ := tailShort)]
                      _ =
                          (consistentFamilyFiniteDimensionalKernel K
                              (fun i ↦ jPrefix (deleteOneIicEmbedding n k i))
                              (hjPrefix.comp (deleteOneIicEmbedding n k).strictMono) x) ⊗ₘ
                            tailShort := by
                              rw [ih (j := jPrefix) (hj := hjPrefix) (k := k)]
                      _ =
                          (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map
                            (succHistoryEquivLocal (E := E) n) := by
                              symm
                              exact hsplitDelete
            _ =
              (consistentFamilyFiniteDimensionalKernel K
                  (fun i ↦ j (deleteOneIicEmbedding (n + 1) k.castSucc i))
                  (hj.comp (deleteOneIicEmbedding (n + 1) k.castSucc).strictMono) x).map
                (succHistoryEquivLocal (E := E) n) := by
                  rfl

/-- Helper for Theorem 14.42: mapping the finite-dimensional chain law along a bottom-preserving
ordered subchain should collapse skipped transitions via consistency. -/
private theorem consistentFamilyFiniteDimensionalKernel_map_subchain [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K)
    (x : E) {n m : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j)
    (e : Finset.Iic m ↪o Finset.Iic n)
    (hzero :
      e ⟨0, Finset.mem_Iic.2 (Nat.zero_le m)⟩ =
        ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩) :
    (consistentFamilyFiniteDimensionalKernel K j hj x).map
        (fun z : (Π _ : Finset.Iic n, E) ↦ fun i : Finset.Iic m ↦ z (e i)) =
      consistentFamilyFiniteDimensionalKernel K (fun i ↦ j (e i)) (hj.comp e.strictMono) x := by
  have hmn : m ≤ n := by
    have hcard := Fintype.card_le_of_embedding e.toEmbedding
    have hmcard : Fintype.card ↥(Finset.Iic m) = m + 1 := by
      rw [Fintype.card_coe, Nat.card_Iic]
    have hncard : Fintype.card ↥(Finset.Iic n) = n + 1 := by
      rw [Fintype.card_coe, Nat.card_Iic]
    rw [hmcard, hncard] at hcard
    exact Nat.succ_le_succ_iff.mp hcard
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst hm
      -- Proof comment: once the unique zero-length subchain is identified with the identity, both
      -- sides are the same measure.
      simpa [orderEmbedding_iic_eq_id e] using
        Measure.map_id (μ := consistentFamilyFiniteDimensionalKernel K j hj x)
  | succ n ih =>
      by_cases hmn_eq : m = n + 1
      · subst hmn_eq
        -- Proof comment: when the subchain has full length, the projection is the identity.
        simpa [orderEmbedding_iic_eq_id e] using
          Measure.map_id (μ := consistentFamilyFiniteDimensionalKernel K j hj x)
      · have hmn' : m ≤ n := by
          exact Nat.le_of_lt_succ (lt_of_le_of_ne hmn hmn_eq)
        rcases factorSubchainThroughDeleteOne hmn' e hzero with ⟨k, e', hfactor, hzero'⟩
        let deleteProjection :
            (Π _ : Finset.Iic (n + 1), E) → Π _ : Finset.Iic n, E :=
          fun z i ↦ z (deleteOneIicEmbedding n k i)
        let subchainProjection :
            (Π _ : Finset.Iic n, E) → Π _ : Finset.Iic m, E :=
          fun z i ↦ z (e' i)
        have hdeleteProjection :
            Measurable deleteProjection := by
          refine measurable_pi_lambda _ ?_
          intro i
          exact measurable_pi_apply (deleteOneIicEmbedding n k i)
        have hsubchainProjection :
            Measurable subchainProjection := by
          refine measurable_pi_lambda _ ?_
          intro i
          exact measurable_pi_apply (e' i)
        have hcomp :
            subchainProjection ∘ deleteProjection =
              (fun z : Π _ : Finset.Iic (n + 1), E ↦
                fun i : Finset.Iic m ↦ z (e i)) := by
          funext z i
          simp [deleteProjection, subchainProjection, hfactor i]
        let jDelete : Π _ : Finset.Iic n, I := fun i ↦ j (deleteOneIicEmbedding n k i)
        let hjDelete : StrictMono jDelete := hj.comp (deleteOneIicEmbedding n k).strictMono
        -- Proof comment: factor the subchain projection into one canonical delete-one map followed
        -- by a shorter bottom-preserving subchain, then recurse on the shorter codomain.
        calc
          (consistentFamilyFiniteDimensionalKernel K j hj x).map
              (fun z : (Π _ : Finset.Iic (n + 1), E) ↦ fun i : Finset.Iic m ↦ z (e i)) =
              ((consistentFamilyFiniteDimensionalKernel K j hj x).map deleteProjection).map
                subchainProjection := by
                  symm
                  rw [Measure.map_map hsubchainProjection hdeleteProjection]
                  exact congrArg
                    (fun f ↦ Measure.map f (consistentFamilyFiniteDimensionalKernel K j hj x)) hcomp
          _ =
              (consistentFamilyFiniteDimensionalKernel K jDelete hjDelete x).map
                subchainProjection := by
                  rw [consistentFamilyFiniteDimensionalKernel_map_deleteOneCanonical
                    (I := I) (E := E) (K := K) (hMarkov := hMarkov)
                    (hConsistent := hConsistent) (x := x) (j := j) (hj := hj) (k := k)]
          _ =
              consistentFamilyFiniteDimensionalKernel K
                (fun i ↦ jDelete (e' i)) (hjDelete.comp e'.strictMono) x := by
                  simpa [subchainProjection, jDelete] using
                    ih (m := m) (j := jDelete) (hj := hjDelete) (e := e')
                      (hzero := hzero') hmn'
          _ =
              consistentFamilyFiniteDimensionalKernel K
                (fun i ↦ j (e i)) (hj.comp e.strictMono) x := by
                  have hchain :
                      (fun i : Finset.Iic m ↦ jDelete (e' i)) =
                        (fun i : Finset.Iic m ↦ j (e i)) := by
                    funext i
                    simp [jDelete, hfactor i]
                  simpa [hchain]

/-- Helper for Theorem 14.42: every finite subset sits inside its enlargement by `⊥`. -/
private theorem subset_insert_bot [OrderBot I] (J : Finset I) : J ⊆ insert ⊥ J := by
  intro i hi
  exact Finset.mem_insert_of_mem hi

/-- Helper for Theorem 14.42: `⊥` belongs to the finite-set enlargement `insert ⊥ J`. -/
private theorem bot_mem_insert_bot [OrderBot I] (J : Finset I) : ⊥ ∈ insert ⊥ J := by
  simp

/-- Helper for Theorem 14.42: reindex a chain tuple by the ordered finite set it enumerates. -/
private theorem measurable_orderedFiniteSetTuple [OrderBot I]
    (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Measurable
      (fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
        fun j : J ↦ z ((orderedFiniteSetOrderIso J hJ0).symm j)) := by
  -- Proof comment: every target coordinate is just one source coordinate picked out by the
  -- inverse ordered enumeration.
  refine measurable_pi_lambda _ ?_
  intro j
  exact measurable_pi_apply ((orderedFiniteSetOrderIso J hJ0).symm j)

/-- Helper for Theorem 14.42: the ordered finite-dimensional law on a finite set containing `⊥`. -/
private noncomputable def pathFamilyWithBot [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) (x : E)
    (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Measure (Π j : J, E) :=
  (consistentFamilyFiniteDimensionalKernel K
      (orderedFiniteSetChain J hJ0)
      (orderedFiniteSetChain_strictMono J hJ0) x).map
    (fun z j ↦ z ((orderedFiniteSetOrderIso J hJ0).symm j))

/-- Helper for Theorem 14.42: the finite-subset law obtained by first adjoining `⊥` and then
restricting back to the requested coordinates. -/
private noncomputable def pathFamilyAt [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) (x : E) (J : Finset I) :
    Measure (Π j : J, E) :=
  (pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J)).map
    (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J))

/-- Helper for Theorem 14.42: the `⊥`-containing ordered finite-subset law is a probability
measure. -/
private theorem pathFamilyWithBot_isProbability [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (x : E) (J : Finset I) (hJ0 : ⊥ ∈ J) :
    IsProbabilityMeasure (pathFamilyWithBot K x J hJ0) := by
  letI :
      IsMarkovKernel
        (consistentFamilyFiniteDimensionalKernel K
          (orderedFiniteSetChain J hJ0)
          (orderedFiniteSetChain_strictMono J hJ0)) :=
    consistentFamilyFiniteDimensionalKernel_isMarkov K hMarkov
      (orderedFiniteSetChain J hJ0) (orderedFiniteSetChain_strictMono J hJ0)
  -- Proof comment: the chain law is Markov, so its pushforward along the reindexing map is still
  -- a probability measure.
  simpa [pathFamilyWithBot] using
    Measure.isProbabilityMeasure_map
      (measurable_orderedFiniteSetTuple (E := E) J hJ0).aemeasurable

/-- Helper for Theorem 14.42: every finite-subset law `pathFamilyAt` is a probability measure. -/
private theorem pathFamilyAt_isProbability [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (x : E) (J : Finset I) :
    IsProbabilityMeasure (pathFamilyAt K x J) := by
  letI :
      IsProbabilityMeasure (pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J)) :=
    pathFamilyWithBot_isProbability (E := E) K hMarkov x (insert ⊥ J) (bot_mem_insert_bot J)
  -- Proof comment: restricting a probability law to fewer coordinates preserves total mass `1`.
  have hMapProb :
      IsProbabilityMeasure
        ((pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J)).map
          (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J))) :=
    Measure.isProbabilityMeasure_map
      (μ := pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J))
      (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot J)).aemeasurable
  simpa [pathFamilyAt] using hMapProb

/-- Helper for Theorem 14.42: finite-subset evaluations of `pathFamilyAt` are measurable in the
initial state. -/
private theorem measurable_pathFamilyAt_apply [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (J : Finset I) {A : Set (Π j : J, E)} (hA : MeasurableSet A) :
    Measurable (fun x ↦ pathFamilyAt K x J A) := by
  let Jbot : Finset I := insert ⊥ J
  let rJ : (Π i : Jbot, E) → Π j : J, E :=
    Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)
  have hRestrict :
      MeasurableSet (rJ ⁻¹' A) :=
    hA.preimage (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot J))
  have hOrdered :
      MeasurableSet
        ((fun z : (Π _ : Finset.Iic (Jbot.card - 1), E) ↦
            fun j : Jbot ↦
              z ((orderedFiniteSetOrderIso Jbot (bot_mem_insert_bot J)).symm j))
          ⁻¹' (rJ ⁻¹' A)) :=
    hRestrict.preimage
      (measurable_orderedFiniteSetTuple (E := E) Jbot (bot_mem_insert_bot J))
  -- Proof comment: expand `pathFamilyAt` into the ordered chain law and use the owner
  -- measurability of finite-dimensional kernel evaluations.
  have hPathFamilyAt :
      (fun x ↦ pathFamilyAt K x J A) =
        fun x ↦ pathFamilyWithBot K x Jbot (bot_mem_insert_bot J) (rJ ⁻¹' A) := by
    funext x
    rw [pathFamilyAt, Measure.map_apply
      (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot J)) hA]
  rw [hPathFamilyAt]
  have hPathFamilyWithBot :
      (fun x ↦ pathFamilyWithBot K x Jbot (bot_mem_insert_bot J) (rJ ⁻¹' A)) =
        fun x ↦
          consistentFamilyFiniteDimensionalKernel K
              (orderedFiniteSetChain Jbot (bot_mem_insert_bot J))
              (orderedFiniteSetChain_strictMono Jbot (bot_mem_insert_bot J)) x
            ((fun z : (Π _ : Finset.Iic (Jbot.card - 1), E) ↦
                fun j : Jbot ↦ z ((orderedFiniteSetOrderIso Jbot (bot_mem_insert_bot J)).symm j))
              ⁻¹' (rJ ⁻¹' A)) := by
    funext x
    rw [pathFamilyWithBot, Measure.map_apply
      (measurable_orderedFiniteSetTuple (E := E) Jbot (bot_mem_insert_bot J)) hRestrict]
  rw [hPathFamilyWithBot]
  exact measurable_consistentFamilyFiniteDimensionalKernel_apply K hMarkov
    (orderedFiniteSetChain Jbot (bot_mem_insert_bot J))
    (orderedFiniteSetChain_strictMono Jbot (bot_mem_insert_bot J)) hOrdered

/-- Helper for Theorem 14.42: the image of a strict finite chain has the expected cardinality. -/
private theorem card_image_strictChain [OrderBot I]
    {n : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) :
    (Finset.image j (Finset.Iic n).attach).card = n + 1 := by
  classical
  rw [Finset.card_image_of_injective _ hj.injective]
  simp

/-- Helper for Theorem 14.42: if a strict chain starts at `⊥`, then the canonical ordered
enumeration of its image recovers the original chain after the obvious index cast. -/
private theorem orderedFiniteSetChain_image_eq [OrderBot I]
    {n : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j)
    (h0 : j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = ⊥) :
    let J : Finset I := Finset.image j Finset.univ
    let hJ0 : ⊥ ∈ J :=
      Finset.mem_image.mpr
        ⟨⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩, Finset.mem_univ _, h0⟩
    ∀ i : Finset.Iic n,
      orderedFiniteSetChain J hJ0
          ⟨i.1, by
            dsimp [J]
            rw [card_image_strictChain (I := I) j hj]
            simpa [Finset.mem_Iic] using i.2⟩ = j i := by
  classical
  intro J hJ0 i
  let jFin : Fin (n + 1) → I := fun k ↦ j (finToIicLocal n k)
  have hjFin_mem : ∀ x, jFin x ∈ J := by
    intro x
    dsimp [jFin, J]
    exact Finset.mem_image.mpr ⟨finToIicLocal n x, Finset.mem_univ _, rfl⟩
  have hjFin_strictMono : StrictMono jFin := by
    intro a b hab
    exact hj (by cases a; cases b; simpa [jFin, finToIicLocal] using hab)
  have hjFin_eq : jFin = J.orderEmbOfFin (by
      dsimp [J]
      exact card_image_strictChain (I := I) j hj) := by
    exact Finset.orderEmbOfFin_unique _ hjFin_mem hjFin_strictMono
  -- Proof comment: `orderedFiniteSetChain` is built from `J.orderEmbOfFin`; once the image of
  -- `j` is identified with `J`, uniqueness of increasing enumerations reduces the claim to index
  -- equality.
  dsimp [orderedFiniteSetChain, orderedFiniteSetOrderIso]
  simp [iicOrderIsoFinLocal, iicToFinLocal]
  rw [show j i = jFin (iicToFinLocal n i) by rfl, hjFin_eq]
  exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff).2 rfl

/-- Helper for Theorem 14.42: the direct subset-marginal comparison for `pathFamilyWithBot` is the
missing projectivity bridge. -/
private theorem pathFamilyWithBot_map_eq_of_subset [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K) (x : E)
    (L J : Finset I) (hLJ : L ⊆ J) (hL0 : ⊥ ∈ L) (hJ0 : ⊥ ∈ J) :
    (pathFamilyWithBot K x J hJ0).map (Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) =
      pathFamilyWithBot K x L hL0 := by
  let e : Finset.Iic (L.card - 1) ↪o Finset.Iic (J.card - 1) :=
    orderedFiniteSetSubsetEmbedding L J hLJ hL0 hJ0
  let subchainProjection :
      (Π _ : Finset.Iic (J.card - 1), E) → Π _ : Finset.Iic (L.card - 1), E :=
    fun z i ↦ z (e i)
  have hSubchainProjection :
      Measurable subchainProjection :=
    measurable_orderedSubchainProjection (E := E) L J hLJ hL0 hJ0
  have hzero :
      e ⟨0, Finset.mem_Iic.2 (Nat.zero_le (L.card - 1))⟩ =
        ⟨0, Finset.mem_Iic.2 (Nat.zero_le (J.card - 1))⟩ := by
    apply (orderedFiniteSetChain_strictMono J hJ0).injective
    -- Proof comment: both candidate indices correspond to the bottom time `⊥` in the ordered
    -- chains of `L` and `J`.
    calc
      orderedFiniteSetChain J hJ0
          (e ⟨0, Finset.mem_Iic.2 (Nat.zero_le (L.card - 1))⟩) =
          orderedFiniteSetChain L hL0 ⟨0, Finset.mem_Iic.2 (Nat.zero_le (L.card - 1))⟩ := by
            simpa [e, subchainProjection] using
              orderedFiniteSetChain_comp_subsetEmbedding (I := I) L J hLJ hL0 hJ0
                ⟨0, Finset.mem_Iic.2 (Nat.zero_le (L.card - 1))⟩
      _ = ⊥ :=
        orderedFiniteSetChain_zero (I := I) L hL0
      _ = orderedFiniteSetChain J hJ0 ⟨0, Finset.mem_Iic.2 (Nat.zero_le (J.card - 1))⟩ := by
        symm
        exact orderedFiniteSetChain_zero (I := I) J hJ0
  have hTransport :
      (Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) ∘
          (fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
            fun j : J ↦ z ((orderedFiniteSetOrderIso J hJ0).symm j)) =
        (fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
          fun i : L ↦ subchainProjection z ((orderedFiniteSetOrderIso L hL0).symm i)) := by
    -- Proof comment: this is exactly the previously extracted reindexing identity between the
    -- ambient tuple restriction and the selected ordered subchain.
    simpa [subchainProjection, e] using
      restrict_orderedFiniteSetTuple_eq_comp_orderedSubchainProjection (E := E)
        L J hLJ hL0 hJ0
  -- Proof comment: once the transport is normalized, the remaining content is the ordered
  -- subchain marginal theorem for `consistentFamilyFiniteDimensionalKernel`.
  let μJ :=
    (consistentFamilyFiniteDimensionalKernel K
      (orderedFiniteSetChain J hJ0)
      (orderedFiniteSetChain_strictMono J hJ0) x)
  let tupleJ :
      (Π _ : Finset.Iic (J.card - 1), E) → Π j : J, E :=
    fun z j ↦ z ((orderedFiniteSetOrderIso J hJ0).symm j)
  let tupleL :
      (Π _ : Finset.Iic (L.card - 1), E) → Π j : L, E :=
    fun z j ↦ z ((orderedFiniteSetOrderIso L hL0).symm j)
  have hMapLeft :
      Measure.map (Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) (Measure.map tupleJ μJ) =
        Measure.map ((Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) ∘ tupleJ) μJ := by
    simpa [μJ, tupleJ] using
      (Measure.map_map
        (μ := μJ)
        (f := tupleJ)
        (g := Finset.restrict₂ (π := fun _ : I ↦ E) hLJ)
        (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) hLJ)
        (measurable_orderedFiniteSetTuple (E := E) J hJ0))
  have hMapRight :
      Measure.map ((fun z : (Π _ : Finset.Iic (J.card - 1), E) ↦
          fun i : L ↦ subchainProjection z ((orderedFiniteSetOrderIso L hL0).symm i))) μJ =
        Measure.map tupleL (Measure.map subchainProjection μJ) := by
    simpa [μJ, tupleL, subchainProjection] using
      (Measure.map_map
        (μ := μJ)
        (f := subchainProjection)
        (g := tupleL)
        (measurable_orderedFiniteSetTuple (E := E) L hL0)
        hSubchainProjection).symm
  rw [pathFamilyWithBot, pathFamilyWithBot, hMapLeft, hTransport, hMapRight]
  have hChainEq :
      (fun i : Finset.Iic (L.card - 1) ↦ orderedFiniteSetChain J hJ0 (e i)) =
        orderedFiniteSetChain L hL0 := by
    funext i
    exact orderedFiniteSetChain_comp_subsetEmbedding (I := I) L J hLJ hL0 hJ0 i
  congr 1
  simpa [μJ, subchainProjection, e, hChainEq] using
    consistentFamilyFiniteDimensionalKernel_map_subchain (I := I) (E := E) K hMarkov
      hConsistent x (orderedFiniteSetChain J hJ0)
      (orderedFiniteSetChain_strictMono J hJ0) e hzero

/-- Helper for Theorem 14.42: the finite-subset family `pathFamilyAt` is projective. -/
private theorem pathFamilyAt_isProjectiveMeasureFamily [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K) (x : E) :
    IsProjectiveMeasureFamily (α := fun _ : I ↦ E) (pathFamilyAt K x) := by
  intro J L hLJ
  have hInsert : insert ⊥ L ⊆ insert ⊥ J := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hiL
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hLJ hiL)
  have hComp :
      (Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) ∘
          (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) =
        (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot L)) ∘
          (Finset.restrict₂ (π := fun _ : I ↦ E) hInsert) := by
    funext z i
    rfl
  -- Proof comment: projectivity is exactly the previously isolated subset-marginal theorem after
  -- one normalization of the two restriction maps through `insert ⊥`.
  calc
    pathFamilyAt K x L =
        Measure.map
          (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot L))
          (pathFamilyWithBot K x (insert ⊥ L) (bot_mem_insert_bot L)) := by
      rw [pathFamilyAt]
    _ =
        Measure.map
          (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot L))
          (Measure.map
            (Finset.restrict₂ (π := fun _ : I ↦ E) hInsert)
            (pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J))) := by
      rw [pathFamilyWithBot_map_eq_of_subset (E := E) K hMarkov hConsistent x
        (insert ⊥ L) (insert ⊥ J) hInsert (bot_mem_insert_bot L) (bot_mem_insert_bot J)]
    _ =
        Measure.map
          ((Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot L)) ∘
            (Finset.restrict₂ (π := fun _ : I ↦ E) hInsert))
          (pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J)) := by
      rw [Measure.map_map
        (f := Finset.restrict₂ (π := fun _ : I ↦ E) hInsert)
        (g := Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot L))
        (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot L))
        (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) hInsert)]
    _ =
        Measure.map
          ((Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) ∘
            (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)))
          (pathFamilyWithBot K x (insert ⊥ J) (bot_mem_insert_bot J)) := by
      rw [hComp]
    _ =
        Measure.map (Finset.restrict₂ (π := fun _ : I ↦ E) hLJ) (pathFamilyAt K x J) := by
      rw [pathFamilyAt, Measure.map_map
        (f := Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J))
        (g := Finset.restrict₂ (π := fun _ : I ↦ E) hLJ)
        (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) hLJ)
        (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot J))]

/-- Helper for Theorem 14.42: if `J` already contains `⊥`, then `pathFamilyAt` is just the
ordered finite-subset law on `J`. -/
private theorem pathFamilyAt_eq_pathFamilyWithBot_of_bot_mem [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K) (x : E) (J : Finset I) (hJ0 : ⊥ ∈ J) :
    pathFamilyAt K x J = pathFamilyWithBot K x J hJ0 := by
  -- Proof comment: once `⊥` is already present, adjoining it does nothing and the required
  -- equality is the subset-marginal theorem with `L = J`.
  simpa [pathFamilyAt] using
    pathFamilyWithBot_map_eq_of_subset (E := E) K hMarkov hConsistent x J (insert ⊥ J)
      (subset_insert_bot J) hJ0 (bot_mem_insert_bot J)

/-- Helper for Theorem 14.42: the lookup map from the image-indexed tuple back to the original
strict chain is measurable. -/
private theorem measurable_lookup_imageChain [OrderBot I]
    {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    let J : Finset I := Finset.image j Finset.univ
    let lookup : (Π y : J, E) → Π _ : Finset.Iic n, E :=
      fun y i ↦ y ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    Measurable lookup := by
  intro J lookup
  -- Proof comment: each output coordinate is evaluation at the corresponding image point.
  refine measurable_pi_lambda _ ?_
  intro i
  exact measurable_pi_apply
    ((⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ : J))

/-- Helper for Theorem 14.42: the lookup map composed with the full path restriction is exactly the
finite-coordinate projection associated to `j`. -/
private theorem lookup_comp_restrict_image_eq_finiteCoordinateProjection [OrderBot I]
    {n : ℕ} (j : Π _ : Finset.Iic n, I) :
    let J : Finset I := Finset.image j Finset.univ
    let lookup : (Π y : J, E) → Π _ : Finset.Iic n, E :=
      fun y i ↦ y ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    lookup ∘ J.restrict = finiteCoordinateProjection j := by
  intro J lookup
  -- Proof comment: both sides evaluate the path at the same time `j i`.
  funext ω i
  simp [lookup, finiteCoordinateProjection]

/-- Helper for Theorem 14.42: transporting an `Iic`-indexed measure across an equality of lengths
only changes the codomain type by the canonical cast. -/
private theorem measure_map_iicCast {n m : ℕ}
    (h : n = m) (μ : Measure (Π _ : Finset.Iic n, E)) :
    μ.map (cast (by cases h; rfl :
      (Π _ : Finset.Iic n, E) = (Π _ : Finset.Iic m, E))) = h ▸ μ := by
  cases h
  change μ.map id = μ
  exact Measure.map_id

/-- Helper for Theorem 14.42: equal `Iic` lengths give a canonical order isomorphism. -/
private def iicCongrOrderIso {n m : ℕ} (h : n = m) : Finset.Iic n ≃o Finset.Iic m where
  toFun i := ⟨i.1, by simpa [h] using i.2⟩
  invFun i := ⟨i.1, by simpa [h] using i.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl
  map_rel_iff' := by
    intro i j
    rfl

/-- Helper for Theorem 14.42: `piCongrLeft` along an equality of `Iic` lengths is the canonical
cast between the two tuple types. -/
private theorem piCongrLeft_iicCongr_eq_cast {n m : ℕ} (h : n = m) :
    ((MeasurableEquiv.piCongrLeft (fun _ : Finset.Iic m ↦ E) (iicCongrOrderIso h).toEquiv) :
        (Π _ : Finset.Iic n, E) → Π _ : Finset.Iic m, E) =
      cast (by cases h; rfl : (Π _ : Finset.Iic n, E) = (Π _ : Finset.Iic m, E)) := by
  -- Proof comment: after rewriting by the index equality, the reindexing map is literally the
  -- identity on tuple spaces.
  cases h
  rfl

/-- Helper for Theorem 14.42: transporting the finite-dimensional kernel across an equality of
`Iic` lengths reindexes the chain by the canonical order isomorphism. -/
private theorem consistentFamilyFiniteDimensionalKernel_iicCongr
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n m : ℕ}
    (h : n = m) (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) (x : E) :
    h ▸ consistentFamilyFiniteDimensionalKernel K j hj x =
      consistentFamilyFiniteDimensionalKernel K
        (fun i : Finset.Iic m ↦ j ((iicCongrOrderIso h).symm i))
        (hj.comp (iicCongrOrderIso h).symm.strictMono) x := by
  -- Proof comment: when the two `Iic` lengths coincide, the transported kernel is definitionally
  -- the same recursion seen through the canonical order isomorphism.
  cases h
  rfl

/-- Helper for Theorem 14.42: the ordered image chain reindexed by the canonical cardinality
order isomorphism is exactly the original strict chain. -/
private theorem orderedFiniteSetChain_reindex_eq [OrderBot I]
    {n : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j)
    (h0 : j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = ⊥) :
    let J : Finset I := Finset.image j Finset.univ
    let hJ0 : ⊥ ∈ J :=
      Finset.mem_image.mpr
        ⟨⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩, Finset.mem_univ _, h0⟩
    let hcard : J.card - 1 = n := by
      dsimp [J]
      rw [card_image_strictChain (I := I) j hj]
      simp
    let e : Finset.Iic (J.card - 1) ≃o Finset.Iic n := iicCongrOrderIso hcard
    (fun i : Finset.Iic n ↦ orderedFiniteSetChain J hJ0 (e.symm i)) = j := by
  intro J hJ0 hcard e
  -- Proof comment: `orderedFiniteSetChain_image_eq` already identifies the ordered image
  -- enumeration with `j`; the new order isomorphism packages the old cast into one reindex map.
  funext i
  simpa [e, iicCongrOrderIso, J, hJ0] using
    (orderedFiniteSetChain_image_eq (I := I) (j := j) hj h0 i)

/-- Helper for Theorem 14.42: the lookup map after ordered-tuple reindexing is the canonical
`piCongrLeft` transport induced by the image-cardinality order isomorphism. -/
private theorem lookupCompOrderedFiniteSetTuple_eq_piCongrLeft [OrderBot I]
    {n : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j)
    (h0 : j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = ⊥) :
    let J : Finset I := Finset.image j Finset.univ
    let hJ0 : ⊥ ∈ J :=
      Finset.mem_image.mpr
        ⟨⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩, Finset.mem_univ _, h0⟩
    let hcard : J.card - 1 = n := by
      dsimp [J]
      rw [card_image_strictChain (I := I) j hj]
      simp
    let e : Finset.Iic (J.card - 1) ≃o Finset.Iic n := iicCongrOrderIso hcard
    let tupleJ :
        (Π _ : Finset.Iic (J.card - 1), E) → Π y : J, E :=
      fun z y ↦ z ((orderedFiniteSetOrderIso J hJ0).symm y)
    let lookup : (Π y : J, E) → Π _ : Finset.Iic n, E :=
      fun y i ↦ y ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    lookup ∘ tupleJ = MeasurableEquiv.piCongrLeft (fun _ : Finset.Iic n ↦ E) e := by
  intro J hJ0 hcard e tupleJ lookup
  -- Proof comment: both maps read the ordered-image tuple at the unique index corresponding to
  -- `j i`; the new route expresses that index transport via `piCongrLeft` instead of a raw cast.
  funext z i
  have hIndex :
      (orderedFiniteSetOrderIso J hJ0).symm
          ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ =
        e.symm i := by
    have hOrdered :
        orderedFiniteSetChain J hJ0 (e.symm i) = j i := by
      simpa using congrFun
        (orderedFiniteSetChain_reindex_eq (I := I) (j := j) hj h0 : _) i
    apply (orderedFiniteSetChain_strictMono J hJ0).injective
    simpa [orderedFiniteSetChain] using hOrdered.symm
  have hValue :
      tupleJ z ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩ = z (e.symm i) := by
    simpa [tupleJ] using congrArg z hIndex
  simpa [tupleJ, lookup, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast] using
    hValue

/-- Helper for Theorem 14.42: mapping the ordered-image finite-dimensional kernel through the
canonical `piCongrLeft` reindex recovers the original `j`-indexed finite-dimensional kernel. -/
private theorem orderedImageKernel_map_piCongrLeft_eq [OrderBot I]
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E) {n : ℕ}
    (j : Π _ : Finset.Iic n, I) (hj : StrictMono j) (x : E)
    (h0 : j ⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩ = ⊥) :
    let J : Finset I := Finset.image j Finset.univ
    let hJ0 : ⊥ ∈ J :=
      Finset.mem_image.mpr
        ⟨⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩, Finset.mem_univ _, h0⟩
    let hcard : J.card - 1 = n := by
      dsimp [J]
      rw [card_image_strictChain (I := I) j hj]
      simp
    Measure.map
        (MeasurableEquiv.piCongrLeft (fun _ : Finset.Iic n ↦ E) (iicCongrOrderIso hcard))
        (consistentFamilyFiniteDimensionalKernel K
          (orderedFiniteSetChain J hJ0)
          (orderedFiniteSetChain_strictMono J hJ0) x) =
      consistentFamilyFiniteDimensionalKernel K j hj x := by
  -- Proof comment: after eliminating the cardinality equality, the reindexing order isomorphism
  -- becomes the identity and only the ordered-image chain identification remains.
  intro J hJ0 hcard
  let μ :=
    consistentFamilyFiniteDimensionalKernel K
      (orderedFiniteSetChain J hJ0)
      (orderedFiniteSetChain_strictMono J hJ0) x
  let jReindexed : Π _ : Finset.Iic n, I :=
    fun i ↦ orderedFiniteSetChain J hJ0 ((iicCongrOrderIso hcard).symm i)
  let hjReindexed : StrictMono jReindexed :=
    (orderedFiniteSetChain_strictMono J hJ0).comp (iicCongrOrderIso hcard).symm.strictMono
  have hPiCast :
      ((MeasurableEquiv.piCongrLeft (fun _ : Finset.Iic n ↦ E) (iicCongrOrderIso hcard)) :
          (Π _ : Finset.Iic (J.card - 1), E) → Π _ : Finset.Iic n, E) =
        cast (congrArg (fun t => (Π _ : Finset.Iic t, E)) hcard) := by
    simpa using piCongrLeft_iicCongr_eq_cast (E := E) hcard
  have hTransport :
      hcard ▸ μ =
        consistentFamilyFiniteDimensionalKernel K jReindexed hjReindexed x := by
    -- Proof comment: package the tuple-length transport once so the final theorem only sees the
    -- reindexed chain.
    simpa [μ, jReindexed, hjReindexed] using
      (consistentFamilyFiniteDimensionalKernel_iicCongr
        (I := I) (E := E) (K := K) hcard
        (orderedFiniteSetChain J hJ0) (orderedFiniteSetChain_strictMono J hJ0) x)
  have hChain :
      jReindexed = j := by
    -- Proof comment: the ordered image chain, reindexed by the cardinality cast, is the original
    -- chain `j`.
    simpa [jReindexed] using
      (orderedFiniteSetChain_reindex_eq (I := I) (j := j) hj h0 : _)
  calc
    Measure.map
        (MeasurableEquiv.piCongrLeft (fun _ : Finset.Iic n ↦ E) (iicCongrOrderIso hcard))
        μ =
        Measure.map
          (cast (congrArg (fun t => (Π _ : Finset.Iic t, E)) hcard)
            : (Π _ : Finset.Iic (J.card - 1), E) → Π _ : Finset.Iic n, E)
          μ := by
            rw [hPiCast]
    _ = hcard ▸ μ := by
          simpa [μ] using measure_map_iicCast (E := E) hcard μ
    _ = consistentFamilyFiniteDimensionalKernel K jReindexed hjReindexed x := hTransport
    _ = consistentFamilyFiniteDimensionalKernel K j hj x := by
          rw [consistentFamilyFiniteDimensionalKernel_congr
            (K := K) (hj := hjReindexed) (hj' := hj) (hjj' := hChain) (x := x)]

-- Proof sketch: for each initial state `x`, the measures
-- `consistentFamilyFiniteDimensionalKernel K j hj x` form a projective family by the
-- consistency hypothesis. Apply Kolmogorov's extension theorem on the product space `I → E`, then
-- verify measurability in `x` on finite cylinders and extend to all measurable sets.
/-- Theorem 14.42: a consistent family of stochastic kernels on the standard Borel state space `E`
produces a kernel on the path space `E^I` whose finite-dimensional marginals along every strictly
increasing chain `⊥ = j₀ < j₁ < ··· < jₙ` are the iterated kernel laws
`δ_x ⊗ \bigotimes_{k=0}^{n-1} κ_{j_k,j_{k+1}}`. -/
theorem exists_kernel_on_path_space_of_consistent_family
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K) :
    letI : OrderBot I := Subtype.orderBot h0I
    ∃ κ : Kernel E (I → E),
      IsMarkovKernel κ ∧
        ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I) (hj : StrictMono j),
          j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
          (κ x).map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel K j hj x := by
  letI : OrderBot I := Subtype.orderBot h0I
  classical
  have hProjective :
      ∀ x : E, IsProjectiveMeasureFamily (α := fun _ : I ↦ E) (pathFamilyAt K x) := by
    intro x
    exact pathFamilyAt_isProjectiveMeasureFamily (E := E) K hMarkov hConsistent x
  have hProjectiveLimit :
      ∀ x : E, ∃ μ : Measure (I → E),
        IsProjectiveLimit (α := fun _ : I ↦ E) μ (pathFamilyAt K x) := by
    intro x
    letI : ∀ J : Finset I, IsProbabilityMeasure (pathFamilyAt K x J) :=
      fun J ↦ pathFamilyAt_isProbability (E := E) K hMarkov x J
    exact exists_projectiveLimit_of_isProjectiveMeasureFamily
      (I := I) (Ω := fun _ : I ↦ E) (P := pathFamilyAt K x) (hProjective x)
  choose μ hμ using hProjectiveLimit
  let κ : Kernel E (I → E) := {
    toFun := μ
    measurable' := by
      letI : ∀ x : E, IsProbabilityMeasure (μ x) := fun x ↦ by
        letI : ∀ J : Finset I, IsProbabilityMeasure (pathFamilyAt K x J) :=
          fun J ↦ pathFamilyAt_isProbability (E := E) K hMarkov x J
        exact (hμ x).isProbabilityMeasure
      -- Proof comment: cylinder evaluations are exactly the finite-subset laws `pathFamilyAt`,
      -- whose dependence on the initial state is already measurable.
      refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        (S := measurableCylinders (fun _ : I ↦ E))
        generateFrom_measurableCylinders.symm
        isPiSystem_measurableCylinders ?_
      intro s hs
      rcases (mem_measurableCylinders _).1 hs with ⟨J, A, hA, rfl⟩
      have hCylinderEval :
          (fun x ↦ μ x (cylinder J A)) = fun x ↦ pathFamilyAt K x J A := by
        funext x
        simpa using (hμ x).measure_cylinder J hA
      rw [hCylinderEval]
      exact measurable_pathFamilyAt_apply (E := E) K hMarkov J hA }
  refine ⟨κ, ?_, ?_⟩
  · constructor
    intro x
    letI : ∀ J : Finset I, IsProbabilityMeasure (pathFamilyAt K x J) :=
      fun J ↦ pathFamilyAt_isProbability (E := E) K hMarkov x J
    change IsProbabilityMeasure (μ x)
    exact (hμ x).isProbabilityMeasure
  · intro x n j hj h0
    let J : Finset I := Finset.image j Finset.univ
    let hJ0 : ⊥ ∈ J :=
      Finset.mem_image.mpr
        ⟨⟨0, Finset.mem_Iic.2 (Nat.zero_le n)⟩, Finset.mem_univ _, h0⟩
    let lookup : (Π y : J, E) → Π _ : Finset.Iic n, E :=
      fun y i ↦ y ⟨j i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hRestrict :
        (μ x).map J.restrict = pathFamilyAt K x J := by
      simpa [J] using (hμ x J)
    have hLookupMeas : Measurable lookup := by
      simpa [J, lookup] using
        measurable_lookup_imageChain (E := E) (I := I) (j := j)
    have hRestrictMeas : Measurable (J.restrict : (I → E) → Π y : J, E) := by
      fun_prop
    have hProjection :
        lookup ∘ J.restrict = finiteCoordinateProjection j := by
      simpa [J, lookup] using
        lookup_comp_restrict_image_eq_finiteCoordinateProjection (E := E) (I := I) (j := j)
    have hPathLookup :
        (pathFamilyAt K x J).map lookup =
          consistentFamilyFiniteDimensionalKernel K j hj x := by
      have hcard : J.card - 1 = n := by
        dsimp [J]
        rw [card_image_strictChain (I := I) j hj]
        simp
      let e : Finset.Iic (J.card - 1) ≃o Finset.Iic n := iicCongrOrderIso hcard
      let tupleJ :
          (Π _ : Finset.Iic (J.card - 1), E) → Π y : J, E :=
        fun z y ↦ z ((orderedFiniteSetOrderIso J hJ0).symm y)
      have hLookupTuple :
          lookup ∘ tupleJ =
            MeasurableEquiv.piCongrLeft (fun _ : Finset.Iic n ↦ E) e := by
        -- Proof comment: `lookup` after the ordered-image tuple map is exactly the canonical
        -- `piCongrLeft` reindex coming from the image-cardinality order isomorphism.
        simpa [J, hJ0, hcard, e, tupleJ, lookup] using
          lookupCompOrderedFiniteSetTuple_eq_piCongrLeft
            (I := I) (E := E) (j := j) hj h0
      -- Proof comment: rewrite the image-indexed marginal through the ordered enumeration of
      -- `J`, then collapse the remaining reindexing by the single `piCongrLeft` bridge.
      rw [pathFamilyAt_eq_pathFamilyWithBot_of_bot_mem (E := E) K hMarkov hConsistent x J hJ0]
      rw [pathFamilyWithBot]
      rw [Measure.map_map hLookupMeas (measurable_orderedFiniteSetTuple (E := E) J hJ0)]
      rw [hLookupTuple]
      simpa [J, hJ0, hcard, e] using
        orderedImageKernel_map_piCongrLeft_eq
          (I := I) (E := E) K (j := j) hj x h0
    -- Proof comment: the projective-limit marginal on `J = image j univ` becomes the requested
    -- finite-dimensional law after one `map_map` normalization and the ordered-image reindexing.
    change (μ x).map (finiteCoordinateProjection j) =
      consistentFamilyFiniteDimensionalKernel K j hj x
    calc
      (μ x).map (finiteCoordinateProjection j) =
          ((μ x).map J.restrict).map lookup := by
            symm
            rw [Measure.map_map hLookupMeas hRestrictMeas, hProjection]
      _ = (pathFamilyAt K x J).map lookup := by
            rw [hRestrict]
      _ = consistentFamilyFiniteDimensionalKernel K j hj x := hPathLookup

end

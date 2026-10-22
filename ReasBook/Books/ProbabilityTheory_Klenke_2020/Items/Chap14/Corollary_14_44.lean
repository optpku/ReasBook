/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Corollary_14_43
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_41

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- The finite-dimensional coordinate projection of a path indexed by `NNReal`. -/
def finiteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → E) → Fin (n + 1) → E :=
  fun ω i ↦ ω (times i)

-- Proof sketch: each component of the projection is evaluation at the measurable coordinate
-- `times i`; measurability of the tuple-valued map follows from `measurable_pi_lambda`.
/-- Finite-dimensional projections of the canonical path space are measurable. -/
theorem measurable_finiteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Measurable
      (finiteDimensionalProjection times : (NNReal → E) → Fin (n + 1) → E) := by
  -- Proof comment: each coordinate of the projection is an evaluation map on the product path
  -- space, so measurability is checked coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (times i)

private def iicEquivFin (n : ℕ) : Finset.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i.1, Nat.lt_succ_of_le <| Finset.mem_Iic.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_Iic.mpr <| Nat.le_of_lt_succ i.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl

private def orderedTimeChain {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, NNReal :=
  fun i ↦ times (iicEquivFin n i)

private theorem orderedTimeChain_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedTimeChain times) := by
  intro i j hij
  exact htimes (by simpa [orderedTimeChain, iicEquivFin] using hij)

/-- The ordered finite-dimensional distribution kernel attached to a family of transition kernels
`κ t`, started from a fixed initial state and indexed by a strictly increasing time tuple. -/
def markovSemigroupFiniteDimKernel (κ : NNReal → Kernel E E) {n : ℕ}
    (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) :
    Kernel E (Fin (n + 1) → E) :=
  (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
      (orderedTimeChain times) (orderedTimeChain_strictMono htimes)).map
    (fun x i ↦ x ((iicEquivFin n).symm i))

/-- Helper for Corollary 14.44: the universal subtype of `NNReal`, used to invoke the Chapter 14
path-space theorems on a subtype index set. -/
private abbrev UnivTime : Type := ↥(Set.univ : Set NNReal)

/-- Helper for Corollary 14.44: reindex `Finset.Iic n`-tuples as `Fin (n + 1)`-tuples. -/
private noncomputable def iicTupleEquivFin (n : ℕ) :
    (Π _ : Finset.Iic n, E) ≃ᵐ (Fin (n + 1) → E) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin (n + 1) ↦ E) (iicEquivFin n)

/-- Helper for Corollary 14.44: identify `((Set.univ : Set NNReal) → E)` with `NNReal → E`. -/
private noncomputable def univPathEquiv :
    (UnivTime → E) ≃ᵐ (NNReal → E) :=
  MeasurableEquiv.piCongrLeft (fun _ : NNReal ↦ E) (Equiv.Set.univ NNReal)

/-- Helper for Corollary 14.44: view the ordered time chain as a chain in `(Set.univ : Set
NNReal)`. -/
private noncomputable def orderedSubtypeTimeChain {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, UnivTime :=
  fun i ↦ (Equiv.Set.univ NNReal).symm (orderedTimeChain times i)

/-- Helper for Corollary 14.44: the subtype-valued ordered time chain is strictly increasing. -/
private theorem orderedSubtypeTimeChain_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedSubtypeTimeChain times) := by
  -- Proof comment: coercing the subtype chain back to `NNReal` recovers `orderedTimeChain`.
  intro i j hij
  exact orderedTimeChain_strictMono htimes (by simpa [orderedSubtypeTimeChain] using hij)

/-- Helper for Corollary 14.44: the subtype-valued ordered time chain starts from `⊥` when the
original time tuple starts at `0`. -/
private theorem orderedSubtypeTimeChain_zero {n : ℕ} {times : Fin (n + 1) → NNReal}
    (hzero : times 0 = 0) :
    orderedSubtypeTimeChain times ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 := by
  -- Proof comment: the first coordinate of `orderedTimeChain` is `times 0`, which is `0` by
  -- hypothesis, and `⊥` in the universal subtype is the point `0`.
  apply Subtype.ext
  simpa [orderedSubtypeTimeChain, orderedTimeChain, iicEquivFin] using hzero

/-- Helper for Corollary 14.44: read a subtype-valued ordered chain as a `Fin (n + 1)`-indexed
tuple of times in `NNReal`. -/
private def chainAsFinTimes {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime) :
    Fin (n + 1) → NNReal :=
  fun i ↦ j ((iicEquivFin n).symm i)

/-- Helper for Corollary 14.44: reindexing a subtype-valued ordered chain by `Fin (n + 1)`
preserves strict monotonicity. -/
private theorem chainAsFinTimes_strictMono {n : ℕ}
    {j : Π _ : Finset.Iic n, UnivTime} (hj : StrictMono j) :
    StrictMono (chainAsFinTimes j) := by
  -- Proof comment: the `Finset.Iic n ≃ Fin (n + 1)` reindexing is order preserving.
  intro i k hik
  exact hj (by simpa [chainAsFinTimes, iicEquivFin] using hik)

/-- Helper for Corollary 14.44: the `Fin (n + 1)`-reindexed chain starts at `0` when the subtype
chain starts at `⊥`. -/
private theorem chainAsFinTimes_zero {n : ℕ}
    {j : Π _ : Finset.Iic n, UnivTime}
    (hzero : j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0) :
    chainAsFinTimes j 0 = 0 := by
  -- Proof comment: the initial `Iic` coordinate corresponds to `0 : Fin (n + 1)`.
  simpa [chainAsFinTimes, iicEquivFin] using congrArg Subtype.val hzero

/-- Helper for Corollary 14.44: reindexing a `Fin (n + 1)` tuple to `Finset.Iic n` and back
recovers the original subtype chain. -/
private theorem orderedSubtypeTimeChain_chainAsFinTimes {n : ℕ}
    (j : Π _ : Finset.Iic n, UnivTime) :
    orderedSubtypeTimeChain (chainAsFinTimes j) = j := by
  -- Proof comment: both sides are the same chain written through the inverse order equivalence.
  funext i
  ext
  simp [orderedSubtypeTimeChain, orderedTimeChain, chainAsFinTimes, iicEquivFin]

/-- Helper for Corollary 14.44: reindexing an `NNReal` time tuple through the subtype chain and
back recovers the original tuple. -/
private theorem chainAsFinTimes_orderedSubtypeTimeChain {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    chainAsFinTimes (orderedSubtypeTimeChain times) = times := by
  -- Proof comment: the `Finset.Iic n ≃ Fin (n + 1)` bookkeeping cancels after forgetting the
  -- universal-subtype wrapper.
  funext i
  simp [chainAsFinTimes, orderedSubtypeTimeChain, orderedTimeChain, iicEquivFin]

/-- Helper for Corollary 14.44: the finite-dimensional projection on `NNReal → E` is the
transport of the finite-coordinate projection on `((Set.univ : Set NNReal) → E)`. -/
private theorem finiteDimensionalProjection_comp_subtypePathEquiv {n : ℕ}
    (times : Fin (n + 1) → NNReal) :
    (finiteDimensionalProjection times : (NNReal → E) → Fin (n + 1) → E) ∘
        (univPathEquiv : (UnivTime → E) → NNReal → E) =
      (iicTupleEquivFin n : (Π _ : Finset.Iic n, E) → Fin (n + 1) → E) ∘
        (finiteCoordinateProjection (orderedSubtypeTimeChain times) :
          (UnivTime → E) → Π _ : Finset.Iic n, E) := by
  -- Proof comment: both sides read off the same path values, only with different coordinate
  -- bookkeeping on the index type.
  funext ω
  ext i
  change
    ((Equiv.piCongrLeft (fun _ : NNReal ↦ E) (Equiv.Set.univ NNReal)) ω) (times i) =
      ((Equiv.piCongrLeft (fun _ : Fin (n + 1) ↦ E) (iicEquivFin n))
        (finiteCoordinateProjection (orderedSubtypeTimeChain times) ω)) i
  rw [Equiv.piCongrLeft_apply, Equiv.piCongrLeft_apply]
  simp [finiteDimensionalProjection, finiteCoordinateProjection, orderedSubtypeTimeChain,
    orderedTimeChain]

/-- Helper for Corollary 14.44: transporting a full-path measure back to the subtype path space
turns `Fin (n + 1)`-marginals into the chain marginals indexed by `Finset.Iic n`. -/
private theorem finiteCoordinateProjection_comp_subtypePathEquivSymm {n : ℕ}
    (j : Π _ : Finset.Iic n, UnivTime) :
    (finiteCoordinateProjection j : (UnivTime → E) → Π _ : Finset.Iic n, E) ∘
        (univPathEquiv.symm : (NNReal → E) → UnivTime → E) =
      ((iicTupleEquivFin n).symm : (Fin (n + 1) → E) → Π _ : Finset.Iic n, E) ∘
        (finiteDimensionalProjection (chainAsFinTimes j) :
          (NNReal → E) → Fin (n + 1) → E) := by
  -- Proof comment: transporting a full path to the subtype path space and then projecting along
  -- `j` is the same as first projecting along the corresponding `Fin`-indexed chain and then
  -- undoing the `Finset.Iic n ≃ Fin (n + 1)` reindexing.
  funext ω
  ext i
  change
    ((Equiv.piCongrLeft (fun _ : UnivTime ↦ E) (Equiv.Set.univ NNReal).symm) ω)
        (j i) =
      ((Equiv.piCongrLeft (fun _ : Finset.Iic n ↦ E) (iicEquivFin n).symm)
        (finiteDimensionalProjection (chainAsFinTimes j) ω)) i
  rw [Equiv.piCongrLeft_apply, Equiv.piCongrLeft_apply]
  simp [finiteCoordinateProjection, finiteDimensionalProjection, chainAsFinTimes]

/-- Helper for Corollary 14.44: the time-difference kernel family on the universal subtype of
`NNReal`. -/
private def subtypeTimeDifferenceKernel (κ : NNReal → Kernel E E) :
    ∀ ⦃s t : UnivTime⦄, s < t → Kernel E E :=
  fun {s t} _ ↦ κ (t - s)

/-- Helper for Corollary 14.44: the `Fin (n + 1)`-marginal kernel attached to `chainAsFinTimes j`
is exactly the subtype-indexed chain kernel mapped through `iicTupleEquivFin n`. -/
private theorem markovSemigroupFiniteDimKernel_eq_subtypeChainMap
    (κ : NNReal → Kernel E E) {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime) (hj : StrictMono j) :
    markovSemigroupFiniteDimKernel κ (chainAsFinTimes j) (chainAsFinTimes_strictMono hj) =
      Kernel.map
        (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
        (iicTupleEquivFin n) := by
  have hchain :
      orderedTimeChain (chainAsFinTimes j) = fun i ↦ (j i : NNReal) := by
    -- Proof comment: coercing the subtype-valued chain equality back to `NNReal` identifies the
    -- owner chain used by `markovSemigroupFiniteDimKernel`.
    funext i
    exact congrArg Subtype.val (congrFun (orderedSubtypeTimeChain_chainAsFinTimes j) i)
  have hjVal : StrictMono (fun i ↦ (j i : NNReal)) := by
    -- Proof comment: forgetting the subtype wrapper preserves the strict order of the chain.
    intro i k hik
    exact hj hik
  have hambient :
      consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
          (orderedTimeChain (chainAsFinTimes j))
          (orderedTimeChain_strictMono (chainAsFinTimes_strictMono hj)) =
        consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
          (fun i ↦ (j i : NNReal)) hjVal := by
    -- Proof comment: after replacing the owner chain by its coerced subtype description, the
    -- strict-monotonicity witness changes only by proof irrelevance.
    cases hchain
    rfl
  have hbase :
      consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
          (fun i ↦ (j i : NNReal)) hjVal =
        consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj := by
    -- Proof comment: the owner finite-dimensional law only sees the underlying times and the
    -- kernels `κ (t - s)`, which are identical for the subtype chain and its coerced values.
    ext x s hs
    rw [consistentFamilyFiniteDimensionalKernel, consistentFamilyFiniteDimensionalKernel]
    congr 1
  have htuple :
      (fun z : (Π _ : Finset.Iic n, E) ↦ fun i : Fin (n + 1) ↦ z ((iicEquivFin n).symm i)) =
        (iicTupleEquivFin n : (Π _ : Finset.Iic n, E) → Fin (n + 1) → E) := by
    -- Proof comment: `iicTupleEquivFin` is exactly the canonical tuple reindexing map.
    funext z i
    rw [iicTupleEquivFin, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  -- Proof comment: once the owner chain is rewritten to the coerced subtype chain, the finite-
  -- dimensional kernel and the tuple reindexing map are definitionally the subtype-chain ones.
  calc
    markovSemigroupFiniteDimKernel κ (chainAsFinTimes j) (chainAsFinTimes_strictMono hj) =
        Kernel.map
          (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
            (orderedTimeChain (chainAsFinTimes j))
            (orderedTimeChain_strictMono (chainAsFinTimes_strictMono hj)))
          (iicTupleEquivFin n) := by
      rw [markovSemigroupFiniteDimKernel, htuple]
    _ =
        Kernel.map
          (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
            (fun i ↦ (j i : NNReal)) hjVal)
          (iicTupleEquivFin n) := by
      rw [hambient]
    _ =
        Kernel.map
          (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
          (iicTupleEquivFin n) := by
      rw [hbase]

/-- Helper for Corollary 14.44: a full-path row measure with the target `Fin (n + 1)`-marginals
induces the Chapter 14 chain marginals on the universal subtype path space. -/
private theorem rowMeasure_hasSubtypeMarginals
    (κ : NNReal → Kernel E E) {x : E} {P : Measure (NNReal → E)}
    (hP :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel κ times htimes x) :
    ∀ {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime),
      ∀ (hj : StrictMono j),
        j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 →
          (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x := by
  intro n j hj hzero
  have hmap :
      (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
        (P.map (finiteDimensionalProjection (chainAsFinTimes j))).map (iicTupleEquivFin n).symm := by
    -- Proof comment: push the subtype-path transport and coordinate projection into one
    -- `Measure.map_map` calculation at the tuple level.
    calc
      (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
          P.map ((finiteCoordinateProjection j) ∘ univPathEquiv.symm) := by
        rw [Measure.map_map
          (f := univPathEquiv.symm)
          (g := finiteCoordinateProjection j)
          (measurable_finiteCoordinateProjection j)
          univPathEquiv.symm.measurable]
      _ = P.map ((iicTupleEquivFin n).symm ∘ finiteDimensionalProjection (chainAsFinTimes j)) := by
        simp [finiteCoordinateProjection_comp_subtypePathEquivSymm j]
      _ = (P.map (finiteDimensionalProjection (chainAsFinTimes j))).map (iicTupleEquivFin n).symm := by
        symm
        rw [Measure.map_map
          (f := finiteDimensionalProjection (chainAsFinTimes j))
          (g := (iicTupleEquivFin n).symm)
          (iicTupleEquivFin n).symm.measurable
          (measurable_finiteDimensionalProjection (chainAsFinTimes j))]
  calc
    (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
        (P.map (finiteDimensionalProjection (chainAsFinTimes j))).map (iicTupleEquivFin n).symm :=
      hmap
    _ =
        (markovSemigroupFiniteDimKernel κ (chainAsFinTimes j)
          (chainAsFinTimes_strictMono hj) x).map (iicTupleEquivFin n).symm := by
      rw [hP (chainAsFinTimes j) (chainAsFinTimes_zero hzero) (chainAsFinTimes_strictMono hj)]
    _ =
        ((Kernel.map
            (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
            (iicTupleEquivFin n)) x).map (iicTupleEquivFin n).symm := by
      rw [markovSemigroupFiniteDimKernel_eq_subtypeChainMap κ j hj]
    _ =
        consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x := by
      ext t ht
      rw [Measure.map_apply (iicTupleEquivFin n).symm.measurable ht]
      rw [Kernel.map_apply' _ (iicTupleEquivFin n).measurable _]
      · simpa using
          congrArg
            (fun u ↦ consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x u)
            ((iicTupleEquivFin n).preimage_symm_preimage t)
      · exact (iicTupleEquivFin n).symm.measurable ht

/-- Helper for Corollary 14.44: a full-path measure with the target `Fin (n + 1)`-marginals
induces the Chapter 14 chain marginals on the universal subtype path space. -/
private theorem measure_hasSubtypeMarginals
    (κ : NNReal → Kernel E E) (μ : Measure E) {P : Measure (NNReal → E)}
    (hP :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          P.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel κ times htimes ∘ₘ μ) :
    ∀ {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime),
      ∀ (hj : StrictMono j),
        j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 →
          (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalMeasure μ (subtypeTimeDifferenceKernel κ) j hj := by
  intro n j hj hzero
  have hmap :
      (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
        (P.map (finiteDimensionalProjection (chainAsFinTimes j))).map (iicTupleEquivFin n).symm := by
    -- Proof comment: this is the same path/tuple transport as in the row-measure lemma.
    calc
      (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
          P.map ((finiteCoordinateProjection j) ∘ univPathEquiv.symm) := by
        rw [Measure.map_map
          (f := univPathEquiv.symm)
          (g := finiteCoordinateProjection j)
          (measurable_finiteCoordinateProjection j)
          univPathEquiv.symm.measurable]
      _ = P.map ((iicTupleEquivFin n).symm ∘ finiteDimensionalProjection (chainAsFinTimes j)) := by
        simp [finiteCoordinateProjection_comp_subtypePathEquivSymm j]
      _ = (P.map (finiteDimensionalProjection (chainAsFinTimes j))).map (iicTupleEquivFin n).symm := by
        symm
        rw [Measure.map_map
          (f := finiteDimensionalProjection (chainAsFinTimes j))
          (g := (iicTupleEquivFin n).symm)
          (iicTupleEquivFin n).symm.measurable
          (measurable_finiteDimensionalProjection (chainAsFinTimes j))]
  have hkernelMapSymm :
      (Kernel.map
          (Kernel.map
            (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
            (iicTupleEquivFin n))
          (iicTupleEquivFin n).symm) =
        consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj := by
    -- Proof comment: cancelling the tuple reindexing measurable equivalence at the kernel level
    -- reduces the mixed-measure transport to the owner finite-dimensional kernel.
    ext x s hs
    rw [Kernel.map_apply' _ (iicTupleEquivFin n).symm.measurable _ hs]
    rw [Kernel.map_apply' _ (iicTupleEquivFin n).measurable _]
    · simpa using
        congrArg
          (fun u ↦ consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x u)
          ((iicTupleEquivFin n).preimage_symm_preimage s)
    · exact (iicTupleEquivFin n).symm.measurable hs
  calc
    (P.map univPathEquiv.symm).map (finiteCoordinateProjection j) =
        (P.map (finiteDimensionalProjection (chainAsFinTimes j))).map (iicTupleEquivFin n).symm :=
      hmap
    _ =
        ((markovSemigroupFiniteDimKernel κ (chainAsFinTimes j)
            (chainAsFinTimes_strictMono hj)) ∘ₘ μ).map (iicTupleEquivFin n).symm := by
      rw [hP (chainAsFinTimes j) (chainAsFinTimes_zero hzero) (chainAsFinTimes_strictMono hj)]
    _ =
        ((Kernel.map
            (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
            (iicTupleEquivFin n)) ∘ₘ μ).map (iicTupleEquivFin n).symm := by
      rw [markovSemigroupFiniteDimKernel_eq_subtypeChainMap κ j hj]
    _ =
        (Kernel.map
          (Kernel.map
            (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
            (iicTupleEquivFin n))
          (iicTupleEquivFin n).symm) ∘ₘ μ := by
      rw [Measure.map_comp μ
        (Kernel.map
          (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
          (iicTupleEquivFin n))
        (iicTupleEquivFin n).symm.measurable]
    _ =
        consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj ∘ₘ μ := by
      rw [hkernelMapSymm]
    _ = consistentFamilyFiniteDimensionalMeasure μ (subtypeTimeDifferenceKernel κ) j hj := by
      rfl

-- Proof sketch: apply Lemma 14.41 to the owner abstraction `IsMarkovSemigroup` to obtain the
-- consistent time-difference kernel family from Theorem 14.42, then use Corollary 14.43 for the
-- corresponding path-space measure statement. Uniqueness is determined by the ordered
-- finite-dimensional marginals.
/-- Corollary 14.44 (1): a Markov semigroup on a Polish space determines a unique path-space
stochastic kernel whose finite-dimensional marginals are the iterated transition laws along every
strictly increasing time tuple starting at `0`. -/
theorem existsUnique_markovPathKernel
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ] :
    ∃! pathKernel : Kernel E (NNReal → E),
      IsMarkovKernel pathKernel ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            pathKernel.map (finiteDimensionalProjection times) =
              markovSemigroupFiniteDimKernel κ times htimes := by
  have hSubtypeMarkov :
      ∀ {s t : UnivTime} (hst : s < t), IsMarkovKernel (subtypeTimeDifferenceKernel κ hst) := by
    -- Proof comment: each time slice of the semigroup is already a Markov kernel.
    intro s t hst
    simpa [subtypeTimeDifferenceKernel] using
      (inferInstance : IsMarkovKernel (κ ((t : NNReal) - (s : NNReal))))
  have hSubtypeConsistent : IsConsistentKernelFamily (subtypeTimeDifferenceKernel κ) := by
    -- Proof comment: Lemma 14.41 applies unchanged after restricting the time index to the
    -- universal subtype of `NNReal`.
    have hBase :
        IsConsistentKernelFamily (fun {s t : NNReal} _ ↦ κ (t - s)) :=
      IsMarkovSemigroup.time_difference_kernels_consistent (κ := κ)
        (show IsMarkovSemigroup κ from inferInstance)
    intro r s t hrs hst
    simpa [subtypeTimeDifferenceKernel] using hBase hrs hst
  rcases exists_kernel_on_path_space_of_consistent_family
      (E := E) (I := (Set.univ : Set NNReal)) (h0I := by simp)
      (K := subtypeTimeDifferenceKernel κ) hSubtypeMarkov hSubtypeConsistent with
    ⟨subtypePathKernel, hSubtypePathKernelMarkov, hSubtypePathKernelMarginals⟩
  let pathKernel : Kernel E (NNReal → E) := Kernel.map subtypePathKernel univPathEquiv
  letI : IsMarkovKernel subtypePathKernel := hSubtypePathKernelMarkov
  have hPathKernelMarkov : IsMarkovKernel pathKernel := by
    -- Proof comment: mapping a Markov kernel along a measurable equivalence preserves the
    -- probability-measure rows.
    simpa [pathKernel] using Kernel.IsMarkovKernel.map subtypePathKernel univPathEquiv.measurable
  have hPathKernelMarginals :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          pathKernel.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel κ times htimes := by
    intro n times hzero htimes
    let j : Π _ : Finset.Iic n, UnivTime := orderedSubtypeTimeChain times
    have hj : StrictMono j := orderedSubtypeTimeChain_strictMono htimes
    have h0j :
        j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 :=
      orderedSubtypeTimeChain_zero hzero
    have hSubtypeProjection :
        subtypePathKernel.map (finiteCoordinateProjection j) =
          consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj := by
      -- Proof comment: Theorem 14.42 gives the required rowwise marginal identity, and ext turns
      -- it into a kernel equality.
      ext x s hs
      have hx :
          ((subtypePathKernel.map (finiteCoordinateProjection j)) x) =
            consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x := by
        simpa [Kernel.map_apply subtypePathKernel
          (measurable_finiteCoordinateProjection j) x] using
          (hSubtypePathKernelMarginals x j hj h0j)
      exact congrArg (fun ν : Measure (Π _ : Finset.Iic n, E) ↦ ν s) hx
    have hPublicKernel :
        Kernel.map
            (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
            (iicTupleEquivFin n) =
          markovSemigroupFiniteDimKernel κ times htimes := by
      have hRaw := markovSemigroupFiniteDimKernel_eq_subtypeChainMap κ j hj
      have hStrict :
          chainAsFinTimes_strictMono hj = htimes := by
        apply Subsingleton.elim
      -- Route correction: the previous transport route was missing the reverse tuple reindexing
      -- `chainAsFinTimes (orderedSubtypeTimeChain times) = times`.
      simpa [j, chainAsFinTimes_orderedSubtypeTimeChain, hStrict] using hRaw.symm
    -- Proof comment: move the subtype-path marginal through `univPathEquiv`, then rewrite the
    -- tuple transport back to the public `markovSemigroupFiniteDimKernel`.
    calc
      (Kernel.map subtypePathKernel univPathEquiv).map (finiteDimensionalProjection times) =
          subtypePathKernel.map ((finiteDimensionalProjection times) ∘ univPathEquiv) := by
        rw [← Kernel.map_comp_right subtypePathKernel univPathEquiv.measurable
          (measurable_finiteDimensionalProjection times)]
      _ =
          subtypePathKernel.map ((iicTupleEquivFin n) ∘ finiteCoordinateProjection j) := by
        rw [finiteDimensionalProjection_comp_subtypePathEquiv times]
      _ =
          (subtypePathKernel.map (finiteCoordinateProjection j)).map (iicTupleEquivFin n) := by
        rw [Kernel.map_comp_right subtypePathKernel
          (measurable_finiteCoordinateProjection j)
          (iicTupleEquivFin n).measurable]
      _ =
          Kernel.map
            (consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj)
            (iicTupleEquivFin n) := by
        rw [hSubtypeProjection]
      _ = markovSemigroupFiniteDimKernel κ times htimes := hPublicKernel
  refine ⟨pathKernel, ?_, ?_⟩
  · exact ⟨hPathKernelMarkov, fun times hzero htimes ↦ hPathKernelMarginals times hzero htimes⟩
  · intro Q hQ
    rcases hQ with ⟨hQMarkov, hQMarginals⟩
    -- Proof comment: compare both candidate rows after transporting them to `UnivTime`, where
    -- Corollary 14.43 gives uniqueness from the consistent chain marginals.
    ext x s hs
    let Qsub : Measure (UnivTime → E) := (Q x).map univPathEquiv.symm
    let Psub : Measure (UnivTime → E) := (pathKernel x).map univPathEquiv.symm
    have hQRowMarginals :
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            (Q x).map (finiteDimensionalProjection times) =
              markovSemigroupFiniteDimKernel κ times htimes x := by
      intro n times hzero htimes
      simpa [Kernel.map_apply Q (measurable_finiteDimensionalProjection times) x] using
        congrArg (fun η : Kernel E (Fin (n + 1) → E) ↦ η x)
          (hQMarginals times hzero htimes)
    have hPRowMarginals :
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            (pathKernel x).map (finiteDimensionalProjection times) =
              markovSemigroupFiniteDimKernel κ times htimes x := by
      intro n times hzero htimes
      simpa [Kernel.map_apply pathKernel (measurable_finiteDimensionalProjection times) x] using
        congrArg (fun η : Kernel E (Fin (n + 1) → E) ↦ η x)
          (hPathKernelMarginals times hzero htimes)
    have hQsubMarginals :
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 →
              Qsub.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure (Measure.dirac x)
                  (subtypeTimeDifferenceKernel κ) j hj := by
      intro n j hj h0
      calc
        Qsub.map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x := by
          simpa [Qsub] using
            rowMeasure_hasSubtypeMarginals (κ := κ) (x := x) (P := Q x) hQRowMarginals j hj h0
        _ =
            consistentFamilyFiniteDimensionalMeasure (Measure.dirac x)
              (subtypeTimeDifferenceKernel κ) j hj := by
          rw [consistentFamilyFiniteDimensionalKernel_apply]
    have hPsubMarginals :
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 →
              Psub.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure (Measure.dirac x)
                  (subtypeTimeDifferenceKernel κ) j hj := by
      intro n j hj h0
      calc
        Psub.map (finiteCoordinateProjection j) =
            consistentFamilyFiniteDimensionalKernel (subtypeTimeDifferenceKernel κ) j hj x := by
          simpa [Psub] using
            rowMeasure_hasSubtypeMarginals (κ := κ) (x := x) (P := pathKernel x)
              hPRowMarginals j hj h0
        _ =
            consistentFamilyFiniteDimensionalMeasure (Measure.dirac x)
              (subtypeTimeDifferenceKernel κ) j hj := by
          rw [consistentFamilyFiniteDimensionalKernel_apply]
    letI : IsMarkovKernel Q := hQMarkov
    have hQsubProb : IsProbabilityMeasure Qsub := by
      letI : IsProbabilityMeasure (Q x) := hQMarkov.isProbabilityMeasure x
      dsimp [Qsub]
      exact Measure.isProbabilityMeasure_map univPathEquiv.symm.measurable.aemeasurable
    have hPsubProb : IsProbabilityMeasure Psub := by
      letI : IsProbabilityMeasure (pathKernel x) := hPathKernelMarkov.isProbabilityMeasure x
      dsimp [Psub]
      exact Measure.isProbabilityMeasure_map univPathEquiv.symm.measurable.aemeasurable
    rcases existsUnique_probabilityMeasure_with_consistent_kernel_marginals
        (E := E) (I := (Set.univ : Set NNReal)) (h0I := by simp)
        (K := subtypeTimeDifferenceKernel κ) hSubtypeMarkov hSubtypeConsistent
        (μ := Measure.dirac x) with
      ⟨P0, hP0, hP0uniq⟩
    have hQsubEq : Qsub = P0 := hP0uniq Qsub ⟨hQsubProb, fun j hj h0 ↦ hQsubMarginals j hj h0⟩
    have hPsubEq : Psub = P0 := hP0uniq Psub ⟨hPsubProb, fun j hj h0 ↦ hPsubMarginals j hj h0⟩
    have hRowEq : Q x = pathKernel x := by
      calc
        Q x = Qsub.map univPathEquiv := by
          simpa [Qsub] using (MeasurableEquiv.map_map_symm (ν := Q x) univPathEquiv)
        _ = Psub.map univPathEquiv := by rw [hQsubEq, hPsubEq]
        _ = pathKernel x := by
          simpa [Psub] using (MeasurableEquiv.map_map_symm (ν := pathKernel x) univPathEquiv)
    exact congrArg (fun ν : Measure (NNReal → E) ↦ ν s) hRowEq

-- Proof sketch: compose the path kernel from the first clause with the initial law `μ`. The
-- resulting measure is a probability measure, and its finite-dimensional marginals are the mixed
-- laws obtained from the finite-dimensional kernel by integrating against `μ`.
/-- Corollary 14.44 (2): every initial probability measure induces a unique probability law on the
path space whose finite-dimensional marginals are obtained by averaging the semigroup kernel from
Corollary 14.44 (1) against the initial law. -/
theorem existsUnique_markovPathMeasure
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    ∃! pathMeasure : Measure (NNReal → E),
      IsProbabilityMeasure pathMeasure ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            pathMeasure.map (finiteDimensionalProjection times) =
              markovSemigroupFiniteDimKernel κ times htimes ∘ₘ μ := by
  rcases existsUnique_markovPathKernel (κ := κ) with
    ⟨pathKernel, hPathKernel, hPathKernelUnique⟩
  letI : IsMarkovKernel pathKernel := hPathKernel.1
  let pathMeasure : Measure (NNReal → E) := pathKernel ∘ₘ μ
  have hPathMeasureProb : IsProbabilityMeasure pathMeasure := by
    -- Proof comment: composing the path kernel with the initial probability law preserves total
    -- mass one.
    dsimp [pathMeasure]
    infer_instance
  have hPathMeasureMarginals :
      ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
        times 0 = 0 → ∀ htimes : StrictMono times,
          pathMeasure.map (finiteDimensionalProjection times) =
            markovSemigroupFiniteDimKernel κ times htimes ∘ₘ μ := by
    intro n times hzero htimes
    -- Proof comment: push the finite-dimensional projection through `pathKernel ∘ₘ μ` and then
    -- substitute the path-kernel marginal identity from the first part.
    calc
      ((pathKernel ∘ₘ μ).map (finiteDimensionalProjection times)) =
          (pathKernel.map (finiteDimensionalProjection times)) ∘ₘ μ := by
        rw [Measure.map_comp μ pathKernel (measurable_finiteDimensionalProjection times)]
      _ = markovSemigroupFiniteDimKernel κ times htimes ∘ₘ μ := by
        rw [hPathKernel.2 times hzero htimes]
  refine ⟨pathMeasure, ?_, ?_⟩
  · exact ⟨hPathMeasureProb, fun times hzero htimes ↦ hPathMeasureMarginals times hzero htimes⟩
  · intro Q hQ
    rcases hQ with ⟨hQProb, hQMarginals⟩
    let Psub : Measure (UnivTime → E) := pathMeasure.map univPathEquiv.symm
    let Qsub : Measure (UnivTime → E) := Q.map univPathEquiv.symm
    have hSubtypeMarkov :
        ∀ {s t : UnivTime} (hst : s < t), IsMarkovKernel (subtypeTimeDifferenceKernel κ hst) := by
      -- Proof comment: the subtype-indexed transition kernels are just the original semigroup
      -- slices at the corresponding time differences.
      intro s t hst
      simpa [subtypeTimeDifferenceKernel] using
        (inferInstance : IsMarkovKernel (κ ((t : NNReal) - (s : NNReal))))
    have hSubtypeConsistent : IsConsistentKernelFamily (subtypeTimeDifferenceKernel κ) := by
      -- Proof comment: the time-difference consistency identity is inherited from the semigroup.
      have hBase :
          IsConsistentKernelFamily (fun {s t : NNReal} _ ↦ κ (t - s)) :=
        IsMarkovSemigroup.time_difference_kernels_consistent (κ := κ)
          (show IsMarkovSemigroup κ from inferInstance)
      intro r s t hrs hst
      simpa [subtypeTimeDifferenceKernel] using hBase hrs hst
    have hQsubMarginals :
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 →
              Qsub.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ (subtypeTimeDifferenceKernel κ) j hj := by
      intro n j hj h0
      simpa [Qsub] using
        measure_hasSubtypeMarginals (κ := κ) (μ := μ) (P := Q) hQMarginals j hj h0
    have hPsubMarginals :
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, UnivTime),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = (Equiv.Set.univ NNReal).symm 0 →
              Psub.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ (subtypeTimeDifferenceKernel κ) j hj := by
      intro n j hj h0
      simpa [Psub] using
        measure_hasSubtypeMarginals (κ := κ) (μ := μ) (P := pathMeasure)
          hPathMeasureMarginals j hj h0
    letI : IsProbabilityMeasure Q := hQProb
    have hQsubProb : IsProbabilityMeasure Qsub := by
      letI : IsProbabilityMeasure Q := hQProb
      dsimp [Qsub]
      exact Measure.isProbabilityMeasure_map univPathEquiv.symm.measurable.aemeasurable
    have hPsubProb : IsProbabilityMeasure Psub := by
      dsimp [Psub]
      exact Measure.isProbabilityMeasure_map univPathEquiv.symm.measurable.aemeasurable
    rcases existsUnique_probabilityMeasure_with_consistent_kernel_marginals
        (E := E) (I := (Set.univ : Set NNReal)) (h0I := by simp)
        (K := subtypeTimeDifferenceKernel κ) hSubtypeMarkov hSubtypeConsistent (μ := μ) with
      ⟨P0, hP0, hP0uniq⟩
    have hQsubEq : Qsub = P0 := hP0uniq Qsub ⟨hQsubProb, fun j hj h0 ↦ hQsubMarginals j hj h0⟩
    have hPsubEq : Psub = P0 := hP0uniq Psub ⟨hPsubProb, fun j hj h0 ↦ hPsubMarginals j hj h0⟩
    calc
      Q = Qsub.map univPathEquiv := by
        simpa [Qsub] using (MeasurableEquiv.map_map_symm (ν := Q) univPathEquiv)
      _ = Psub.map univPathEquiv := by rw [hQsubEq, hPsubEq]
      _ = pathMeasure := by
        simpa [Psub] using (MeasurableEquiv.map_map_symm (ν := pathMeasure) univPathEquiv)

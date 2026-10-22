/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_42

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Preorder Finset
open scoped ProbabilityTheory

noncomputable section

universe u v

variable {I : Type u} [LinearOrder I] [OrderBot I]
variable {E : Type v} [MeasurableSpace E]

/-- Helper for Corollary 14.43: forget the upper-bound proof on `Finset.Iic n`. -/
private def iicToFinLocal (n : ℕ) : Finset.Iic n → Fin (n + 1) :=
  fun i ↦ ⟨i.1, Nat.lt_succ_of_le (Finset.mem_Iic.mp i.2)⟩

/-- Helper for Corollary 14.43: view `Fin (n + 1)` as `Finset.Iic n`. -/
private def finToIicLocal (n : ℕ) : Fin (n + 1) → Finset.Iic n :=
  fun i ↦ ⟨i.1, Finset.mem_Iic.mpr (Nat.le_of_lt_succ i.2)⟩

/-- Helper for Corollary 14.43: `finToIicLocal` is a left inverse to `iicToFinLocal`. -/
private theorem finToIicLocal_leftInv (n : ℕ) :
    Function.LeftInverse (finToIicLocal n) (iicToFinLocal n) := by
  intro i
  cases i
  rfl

/-- Helper for Corollary 14.43: `finToIicLocal` is a right inverse to `iicToFinLocal`. -/
private theorem finToIicLocal_rightInv (n : ℕ) :
    Function.RightInverse (finToIicLocal n) (iicToFinLocal n) := by
  intro i
  cases i
  rfl

/-- Helper for Corollary 14.43: forgetting the upper-bound proof preserves the order on
`Finset.Iic n`. -/
private theorem iicToFinLocal_map_rel_iff (n : ℕ) {i j : Finset.Iic n} :
    iicToFinLocal n i ≤ iicToFinLocal n j ↔ i ≤ j := by
  rfl

/-- Helper for Corollary 14.43: `Finset.Iic n` is canonically order-isomorphic to `Fin (n + 1)`.
-/
private def iicOrderIsoFinLocal (n : ℕ) : Finset.Iic n ≃o Fin (n + 1) where
  toFun := iicToFinLocal n
  invFun := finToIicLocal n
  left_inv := finToIicLocal_leftInv n
  right_inv := finToIicLocal_rightInv n
  map_rel_iff' := iicToFinLocal_map_rel_iff n

/-- Helper for Corollary 14.43: a finite set containing `⊥` is nonempty. -/
private theorem finiteSetNonemptyOfBotMem (J : Finset I) (hJ0 : ⊥ ∈ J) :
    J.Nonempty :=
  ⟨⊥, hJ0⟩

/-- Helper for Corollary 14.43: a finite set containing `⊥` can be ordered as a chain indexed by
`Finset.Iic (J.card - 1)`. -/
private noncomputable def orderedFiniteSetOrderIso (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Finset.Iic (J.card - 1) ≃o ↥J :=
  ((iicOrderIsoFinLocal (J.card - 1)).trans
      (Fin.castOrderIso
        (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr (finiteSetNonemptyOfBotMem J hJ0))))).trans
    (J.orderIsoOfFin rfl)

/-- Helper for Corollary 14.43: the increasing chain enumerating a finite subset containing `⊥`.
-/
private noncomputable def orderedFiniteSetChain (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Π _ : Finset.Iic (J.card - 1), I :=
  fun i ↦ (orderedFiniteSetOrderIso J hJ0 i : I)

/-- Helper for Corollary 14.43: the ordered enumeration of a finite subset is strict. -/
private theorem orderedFiniteSetChain_strictMono (J : Finset I) (hJ0 : ⊥ ∈ J) :
    StrictMono (orderedFiniteSetChain J hJ0) := by
  -- Proof comment: the ordered chain is obtained by coercing an order isomorphism.
  simpa [orderedFiniteSetChain] using (orderedFiniteSetOrderIso J hJ0).strictMono

/-- Helper for Corollary 14.43: the ordered enumeration of a finite subset containing `⊥` starts
at `⊥`. -/
private theorem orderedFiniteSetChain_zero (J : Finset I) (hJ0 : ⊥ ∈ J) :
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
  -- Proof comment: the first element in the increasing enumeration is the minimum of `J`.
  exact hi0_eq_min.trans hmin

/-- Helper for Corollary 14.43: reindex an ordered chain tuple by the corresponding finite subset.
-/
private noncomputable def orderedFiniteSetTuple (J : Finset I) (hJ0 : ⊥ ∈ J) :
    (Π _ : Finset.Iic (J.card - 1), E) → Π j : J, E :=
  fun z j ↦ z ((orderedFiniteSetOrderIso J hJ0).symm j)

/-- Helper for Corollary 14.43: the tuple reindexing map attached to an ordered finite set is
measurable. -/
private theorem measurable_orderedFiniteSetTuple (J : Finset I) (hJ0 : ⊥ ∈ J) :
    Measurable (orderedFiniteSetTuple (E := E) J hJ0) := by
  -- Proof comment: each output coordinate evaluates the source tuple at one fixed index.
  refine measurable_pi_lambda _ ?_
  intro j
  exact measurable_pi_apply ((orderedFiniteSetOrderIso J hJ0).symm j)

/-- Helper for Corollary 14.43: reindexing the ordered-chain coordinates recovers the finite-set
restriction map. -/
private theorem orderedFiniteSetTuple_comp_finiteCoordinateProjection_eq_restrict
    (J : Finset I) (hJ0 : ⊥ ∈ J) :
    orderedFiniteSetTuple (E := E) J hJ0 ∘ finiteCoordinateProjection (orderedFiniteSetChain J hJ0) =
      J.restrict := by
  -- Proof comment: both maps evaluate a path at the same time coordinate for each `j : J`.
  funext ω j
  simp [orderedFiniteSetTuple, finiteCoordinateProjection, orderedFiniteSetChain]

/-- Helper for Corollary 14.43: every finite set sits inside its enlargement by `⊥`. -/
private theorem subset_insert_bot (J : Finset I) : J ⊆ insert ⊥ J := by
  intro i hi
  exact Finset.mem_insert_of_mem hi

/-- Helper for Corollary 14.43: restricting from `insert ⊥ J` back to `J` recovers the original
finite restriction. -/
private theorem restrict_insertBot_comp_eq_restrict (J : Finset I) :
    (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) ∘
        (Finset.restrict (π := fun _ : I ↦ E) (s := insert ⊥ J)) =
      Finset.restrict (π := fun _ : I ↦ E) (s := J) := by
  -- Proof comment: both composite maps forget the same coordinates outside `J`.
  funext ω j
  rfl

-- Proof sketch: first identify the finite restriction to `insert ⊥ J` with the chain marginal
-- coming from the ordered enumeration of `insert ⊥ J`; then restrict back down to `J`.
/-- Helper for Corollary 14.43: equality of all ordered chain marginals starting at `⊥` forces
equality of all finite restrictions. -/
private theorem map_restrict_eq_ofChainMarginals
    (P Q : Measure (I → E))
    (hChain :
      ∀ {n : ℕ} (j : Π _ : Finset.Iic n, I),
        ∀ (hj : StrictMono j),
          j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
            P.map (finiteCoordinateProjection j) = Q.map (finiteCoordinateProjection j)) :
    ∀ J : Finset I, P.map J.restrict = Q.map J.restrict := by
  intro J
  let Jbot : Finset I := insert ⊥ J
  have hJbot0 : ⊥ ∈ Jbot := by
    simp [Jbot]
  let j : Π _ : Finset.Iic (Jbot.card - 1), I := orderedFiniteSetChain Jbot hJbot0
  have hj : StrictMono j := orderedFiniteSetChain_strictMono Jbot hJbot0
  have h0 : j ⟨0, mem_Iic.2 (Nat.zero_le (Jbot.card - 1))⟩ = ⊥ :=
    orderedFiniteSetChain_zero Jbot hJbot0
  let tuple : (Π _ : Finset.Iic (Jbot.card - 1), E) → Π y : Jbot, E :=
    orderedFiniteSetTuple (E := E) Jbot hJbot0
  have hCompTuple :
      tuple ∘ finiteCoordinateProjection j = Jbot.restrict := by
    simpa [tuple, j] using
      orderedFiniteSetTuple_comp_finiteCoordinateProjection_eq_restrict (E := E) Jbot hJbot0
  have hJbot :
      P.map Jbot.restrict = Q.map Jbot.restrict := by
    have hMapP :
        (P.map (finiteCoordinateProjection j)).map tuple = P.map Jbot.restrict := by
      rw [Measure.map_map
        (f := finiteCoordinateProjection j)
        (g := tuple)
        (measurable_orderedFiniteSetTuple (E := E) Jbot hJbot0)
        (measurable_finiteCoordinateProjection j)]
      simp [hCompTuple]
    have hMapQ :
        (Q.map (finiteCoordinateProjection j)).map tuple = Q.map Jbot.restrict := by
      rw [Measure.map_map
        (f := finiteCoordinateProjection j)
        (g := tuple)
        (measurable_orderedFiniteSetTuple (E := E) Jbot hJbot0)
        (measurable_finiteCoordinateProjection j)]
      simp [hCompTuple]
    -- Proof comment: rewrite both finite restrictions as pushforwards of the same ordered chain
    -- reindexing map and then apply the chain-marginal hypothesis.
    calc
      P.map Jbot.restrict = (P.map (finiteCoordinateProjection j)).map tuple := hMapP.symm
      _ = (Q.map (finiteCoordinateProjection j)).map tuple := by
        rw [hChain j hj h0]
      _ = Q.map Jbot.restrict := hMapQ
  have hCompRestrict :
      (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) ∘
          (Finset.restrict (π := fun _ : I ↦ E) (s := Jbot)) =
        Finset.restrict (π := fun _ : I ↦ E) (s := J) := by
    simpa [Jbot] using restrict_insertBot_comp_eq_restrict (E := E) J
  -- Proof comment: once the enlarged finite restrictions agree, restricting away the initial
  -- bottom coordinate gives equality on the original finite set.
  calc
    P.map J.restrict =
        (P.map Jbot.restrict).map (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) := by
      have hMapP :
          (P.map (Finset.restrict (π := fun _ : I ↦ E) (s := Jbot))).map
              (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) =
            P.map (Finset.restrict (π := fun _ : I ↦ E) (s := J)) := by
        rw [Measure.map_map
          (f := Finset.restrict (π := fun _ : I ↦ E) (s := Jbot))
          (g := Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J))
          (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot J))
          (Finset.measurable_restrict (X := fun _ : I ↦ E) Jbot)]
        simp [hCompRestrict]
      simpa using hMapP.symm
    _ =
        (Q.map Jbot.restrict).map (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) := by
      rw [hJbot]
    _ = Q.map J.restrict := by
      have hMapQ :
          (Q.map (Finset.restrict (π := fun _ : I ↦ E) (s := Jbot))).map
              (Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J)) =
            Q.map (Finset.restrict (π := fun _ : I ↦ E) (s := J)) := by
        rw [Measure.map_map
          (f := Finset.restrict (π := fun _ : I ↦ E) (s := Jbot))
          (g := Finset.restrict₂ (π := fun _ : I ↦ E) (subset_insert_bot J))
          (Finset.measurable_restrict₂ (X := fun _ : I ↦ E) (subset_insert_bot J))
          (Finset.measurable_restrict (X := fun _ : I ↦ E) Jbot)]
        simp [hCompRestrict]
      simpa using hMapQ

-- Proof sketch: define the candidate measure as the composition `κpath ∘ₘ μ`. The finite-chain
-- marginal identity follows by integrating the point-mass identity from `hκpath.2` against `μ`;
-- the resulting measure is a probability measure because both `μ` and `κpath` are Markov. For
-- uniqueness, compare finite-dimensional marginals on every ordered finite chain and invoke the
-- usual cylinder/projective-limit uniqueness argument.
/-- Helper for Corollary 14.43: once a path kernel with the finite-dimensional marginals from
Theorem 14.42 is fixed, composing it with an initial probability measure yields the corresponding
unique path-space law. -/
theorem existsUnique_probabilityMeasure_with_consistent_kernel_marginals_of_kernel
    (μ : Measure E) [IsProbabilityMeasure μ]
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (κpath : Kernel E (I → E))
    (hκpath :
      IsMarkovKernel κpath ∧
        ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
              (κpath x).map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalKernel κ j hj x) :
    ∃! P : Measure (I → E),
      IsProbabilityMeasure P ∧
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, I),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
              P.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ κ j hj := by
  letI : IsMarkovKernel κpath := hκpath.1
  let P0 : Measure (I → E) := κpath ∘ₘ μ
  have hP0prob : IsProbabilityMeasure P0 := by
    infer_instance
  have hP0marginals :
      ∀ {n : ℕ} (j : Π _ : Finset.Iic n, I),
        ∀ (hj : StrictMono j),
          j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
            P0.map (finiteCoordinateProjection j) =
              consistentFamilyFiniteDimensionalMeasure μ κ j hj := by
    intro n j hj h0
    have hMapKernel :
        κpath.map (finiteCoordinateProjection j) = consistentFamilyFiniteDimensionalKernel κ j hj := by
      ext x s hs
      have hPoint :
          ((κpath x).map (finiteCoordinateProjection j)) s =
            (consistentFamilyFiniteDimensionalKernel κ j hj x) s :=
        congrArg (fun ν : Measure (Π _ : Finset.Iic n, E) ↦ ν s) (hκpath.2 x j hj h0)
      rw [Kernel.map_apply' _ (measurable_finiteCoordinateProjection j) _ hs]
      simpa [Measure.map_apply (measurable_finiteCoordinateProjection j) hs] using hPoint
    -- Proof comment: push the coordinate projection through the composed measure and use the
    -- prescribed pointwise marginal identity for `κpath`.
    calc
      P0.map (finiteCoordinateProjection j) =
          (κpath.map (finiteCoordinateProjection j)) ∘ₘ μ := by
        rw [Measure.map_comp μ κpath (measurable_finiteCoordinateProjection j)]
      _ = consistentFamilyFiniteDimensionalKernel κ j hj ∘ₘ μ := by
        rw [hMapKernel]
      _ = consistentFamilyFiniteDimensionalMeasure μ κ j hj := by
        rfl
  refine ⟨P0, ?_, ?_⟩
  · exact ⟨hP0prob, fun j hj h0 ↦ hP0marginals j hj h0⟩
  · intro Q hQ
    rcases hQ with ⟨hQprob, hQmarginals⟩
    letI : IsProbabilityMeasure Q := hQprob
    letI : ∀ J : Finset I, IsProbabilityMeasure (P0.map J.restrict) := fun J ↦
      Measure.isProbabilityMeasure_map
        (μ := P0)
        (Finset.measurable_restrict (X := fun _ : I ↦ E) J).aemeasurable
    have hQrestrict :
        ∀ J : Finset I, Q.map J.restrict = P0.map J.restrict := by
      intro J
      exact map_restrict_eq_ofChainMarginals (E := E) Q P0
        (fun j hj h0 ↦ by
          calc
            Q.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ κ j hj := hQmarginals j hj h0
            _ = P0.map (finiteCoordinateProjection j) := (hP0marginals j hj h0).symm) J
    have hP0limit : IsProjectiveLimit P0 (fun J ↦ P0.map J.restrict) := by
      intro J
      rfl
    have hQlimit : IsProjectiveLimit Q (fun J ↦ P0.map J.restrict) := by
      intro J
      exact hQrestrict J
    exact hQlimit.unique hP0limit

section

variable {E : Type v} [MeasurableSpace E] [StandardBorelSpace E]
variable {I : Set NNReal}
variable (h0I : (0 : NNReal) ∈ I)

-- Proof sketch: apply Theorem 14.42 to obtain a path kernel `κpath` with the prescribed
-- point-mass finite-dimensional marginals, then compose it with the initial law `μ` and invoke
-- `existsUnique_probabilityMeasure_with_consistent_kernel_marginals_of_kernel`.
/-- Corollary 14.43: a consistent family of Markov kernels on the standard Borel state space `E`
and an initial probability measure determine a unique probability measure on the path space whose
finite-dimensional marginals are the mixed laws induced by the kernels along every strictly
increasing chain starting at `0`. -/
theorem existsUnique_probabilityMeasure_with_consistent_kernel_marginals
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    letI : OrderBot I := Subtype.orderBot h0I
    ∃! P : Measure (I → E),
      IsProbabilityMeasure P ∧
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, I),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
              P.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ K j hj := by
  letI : OrderBot I := Subtype.orderBot h0I
  -- Proof comment: Theorem 14.42 supplies the path kernel with the required pointwise chain
  -- marginals, and the auxiliary theorem turns it into the unique mixed path measure.
  rcases exists_kernel_on_path_space_of_consistent_family (E := E) (I := I) h0I K hMarkov
      hConsistent with ⟨κpath, hMarkovPath, hMarginals⟩
  exact existsUnique_probabilityMeasure_with_consistent_kernel_marginals_of_kernel
    (μ := μ)
    (κ := K)
    (κpath := κpath)
    ⟨hMarkovPath, hMarginals⟩

end

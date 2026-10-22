/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_17

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

variable {Ω : Type v} [MeasurableSpace Ω]
variable {E : Type u} [MeasurableSpace E]

/-- Helper for Remark 12.9: a permutation of the first `n` coordinates fixes every later
coordinate. -/
private theorem permutePrefix_apply_of_le {E : Type u} {n i : ℕ} (ρ : Equiv.Perm (Fin n))
    (x : ℕ → E)
    (hi : n ≤ i) :
    permutePrefix n ρ x i = x i := by
  -- Tail coordinates lie outside the embedded copy of `Fin n`, so the extended permutation is
  -- the identity there.
  have hfix :
      (ρ.extendDomain Fin.equivSubtype) i = i :=
    Equiv.Perm.extendDomain_apply_not_subtype (e := ρ) (f := Fin.equivSubtype) (b := i)
      (h := Nat.not_lt_of_ge hi)
  simpa [permutePrefix] using congrArg x hfix

/-- Helper for Remark 12.9: the `n`th tail stage of `X` is contained in the `n`-exchangeable
stage of the sample-sequence map. -/
private theorem tailStage_le_nExchangeableSigmaAlgebra {Ω : Type v} (X : ℕ → Ω → E) (n : ℕ) :
    (⨆ i ∈ Set.Ici n, MeasurableSpace.comap (X i) inferInstance) ≤
      nExchangeableSigmaAlgebra (Function.swap X) n := by
  refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
  have hi' : n ≤ i := hi
  have hEval : Measurable[nSymmetricSequenceSigmaAlgebra n] (Function.eval i : (ℕ → E) → E) := by
    rw [measurable_iff_comap_le]
    intro s hs
    rcases (MeasurableSpace.measurableSet_comap.mp hs) with ⟨t, ht, rfl⟩
    rw [measurableSet_nSymmetricSequenceSigmaAlgebra_iff]
    refine ⟨measurableSet_preimage (measurable_pi_apply i) ht, ?_⟩
    intro ρ
    ext x
    simp [permutePrefix_apply_of_le (ρ := ρ) (x := x) hi']
  -- Pull the coordinate measurability back along the sample-sequence map.
  calc
    MeasurableSpace.comap (X i) inferInstance =
        (MeasurableSpace.comap (Function.eval i) inferInstance).comap (Function.swap X) := by
          rw [MeasurableSpace.comap_comp]
          rfl
    _ ≤ (nSymmetricSequenceSigmaAlgebra n).comap (Function.swap X) :=
      MeasurableSpace.comap_mono hEval.comap_le
    _ = nExchangeableSigmaAlgebra (Function.swap X) n := rfl

/-- Helper for Remark 12.9: the event that every coordinate is `false` is ambient measurable on
`Bool` sequence space. -/
private theorem allFalse_measurableSet :
    MeasurableSet ({x : ℕ → Bool | ∀ n, x n = false} : Set (ℕ → Bool)) := by
  -- Rewrite the event as the countable intersection of the coordinate singleton events.
  have hEq :
      ({x : ℕ → Bool | ∀ n, x n = false} : Set (ℕ → Bool)) =
        ⋂ n : ℕ, (Function.eval n) ⁻¹' ({false} : Set Bool) := by
    ext x
    simp
  rw [hEq]
  refine MeasurableSet.iInter fun n ↦ ?_
  exact measurableSet_preimage (measurable_pi_apply n) (measurableSet_singleton false)

/-- Helper for Remark 12.9: the all-false event is invariant under finite prefix permutations. -/
private theorem allFalse_isNSymmetricSequenceSet (n : ℕ) :
    IsNSymmetricSequenceSet n {x : ℕ → Bool | ∀ k, x k = false} := by
  intro ρ
  ext x
  constructor
  · intro hx k
    have hk := hx ((ρ.extendDomain Fin.equivSubtype).symm k)
    have hcancel :
        (ρ.extendDomain Fin.equivSubtype)
            ((Equiv.Perm.extendDomain (Equiv.symm ρ) Fin.equivSubtype) k) = k := by
      simpa [Equiv.Perm.extendDomain_symm] using
        (Equiv.apply_symm_apply (ρ.extendDomain Fin.equivSubtype) k)
    simpa [permutePrefix, hcancel] using hk
  · intro hx k
    have hcancel :
        (ρ.extendDomain Fin.equivSubtype).symm ((ρ.extendDomain Fin.equivSubtype) k) = k :=
      Equiv.symm_apply_apply _ _
    simpa [permutePrefix, hcancel] using hx ((ρ.extendDomain Fin.equivSubtype) k)

/-- Helper for Remark 12.9: the all-false event belongs to every finite exchangeable stage, hence
to the exchangeable `σ`-algebra. -/
private theorem allFalse_measurableSet_mem_exchangeableSequenceSigmaAlgebra :
    MeasurableSet[exchangeableSequenceSigmaAlgebra] {x : ℕ → Bool | ∀ n, x n = false} := by
  -- Reduce exchangeable measurability to the finite stages and check the owner criterion there.
  rw [exchangeableSequenceSigmaAlgebra_eq_iInf_nSymmetricSequenceSigmaAlgebra]
  let A : Set (ℕ → Bool) := {x | ∀ n, x n = false}
  have hGenerate :
      (MeasurableSpace.generateFrom {A} : MeasurableSpace (ℕ → Bool)) ≤
        ⨅ n : ℕ, nSymmetricSequenceSigmaAlgebra n := by
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    rw [measurableSet_nSymmetricSequenceSigmaAlgebra_iff]
    exact ⟨allFalse_measurableSet, allFalse_isNSymmetricSequenceSet n⟩
  have hA : MeasurableSet[MeasurableSpace.generateFrom {A}] A :=
    MeasurableSpace.measurableSet_generateFrom (by simp)
  exact hGenerate A hA

/-- Helper for Remark 12.9: the first tail stage on `Bool` sequence space is the pullback of the
ambient product `σ`-algebra along the one-step shift. -/
private theorem tailStageOne_eq_shiftComap :
    (⨆ i ∈ Set.Ici 1, MeasurableSpace.comap (Function.eval i) inferInstance) =
      MeasurableSpace.comap (fun x : ℕ → Bool => fun n ↦ x (n + 1)) inferInstance := by
  -- Normalize the stage by reindexing coordinates from `1, 2, ...` to `0, 1, ...` after shifting.
  let shift : (ℕ → Bool) → (ℕ → Bool) := fun x n ↦ x (n + 1)
  calc
    (⨆ i ∈ Set.Ici 1, MeasurableSpace.comap (Function.eval i) inferInstance) =
        ⨆ j : ℕ, MeasurableSpace.comap (Function.eval (j + 1)) inferInstance := by
          apply le_antisymm
          · refine iSup_le fun i ↦ iSup_le fun hi ↦ ?_
            rcases Nat.exists_eq_add_of_le hi with ⟨j, rfl⟩
            refine le_iSup_of_le j ?_
            simp [Nat.add_comm]
          · refine iSup_le fun j ↦ ?_
            refine le_iSup_of_le (j + 1) ?_
            exact
              le_iSup_of_le (Nat.succ_le_succ (Nat.zero_le j))
                (le_rfl :
                  MeasurableSpace.comap (Function.eval (j + 1)) inferInstance ≤
                    MeasurableSpace.comap (Function.eval (j + 1)) inferInstance)
    _ = MeasurableSpace.comap shift inferInstance := by
          calc
            (⨆ j : ℕ, MeasurableSpace.comap (Function.eval (j + 1)) inferInstance) =
                ⨆ j : ℕ,
                  MeasurableSpace.comap ((Function.eval j) ∘ shift) inferInstance := by
                      refine iSup_congr fun j ↦ ?_
                      refine congrArg
                        (fun f : (ℕ → Bool) → Bool ↦ MeasurableSpace.comap f inferInstance) ?_
                      funext x
                      rfl
            _ =
                MeasurableSpace.comap shift
                  (⨆ j : ℕ, MeasurableSpace.comap (Function.eval j) inferInstance) := by
                    rw [MeasurableSpace.comap_iSup]
                    simp [MeasurableSpace.comap_comp]
            _ =
                MeasurableSpace.comap shift (inferInstance : MeasurableSpace (ℕ → Bool)) := by
                    rfl
    _ = MeasurableSpace.comap (fun x : ℕ → Bool => fun n ↦ x (n + 1)) inferInstance := rfl

/-- Helper for Remark 12.9: the all-false event is not tail measurable for the coordinate process
on `Bool` sequence space. -/
private theorem allFalse_not_measurableSet_tailRandomVariableMeasurableSpace_eval :
    ¬ MeasurableSet[tailRandomVariableMeasurableSpace
      (Function.eval : ℕ → (ℕ → Bool) → Bool)] {x : ℕ → Bool | ∀ n, x n = false} := by
  intro hA
  let A : Set (ℕ → Bool) := {x | ∀ n, x n = false}
  let shift : (ℕ → Bool) → (ℕ → Bool) := fun x n ↦ x (n + 1)
  have hStage :
      MeasurableSet[
        (⨆ i ∈ Set.Ici 1, MeasurableSpace.comap (Function.eval i) inferInstance)] A := by
    -- Tail measurability implies measurability in each finite tail stage, in particular at stage
    -- `1`.
    have hle :
        tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → Bool) → Bool) ≤
          ⨆ i ∈ Set.Ici 1, MeasurableSpace.comap (Function.eval i) inferInstance := by
      rw [tailRandomVariableMeasurableSpace, tailMeasurableSpace_nat_eq_iInf_iSup_Ici]
      exact iInf_le (fun n ↦ ⨆ i ∈ Set.Ici n, MeasurableSpace.comap (Function.eval i) inferInstance)
        1
    exact hle A hA
  rw [tailStageOne_eq_shiftComap, MeasurableSpace.measurableSet_comap] at hStage
  rcases hStage with ⟨B, _, hBdef⟩
  let x0 : ℕ → Bool := fun _ ↦ false
  let x1 : ℕ → Bool := fun n ↦ if n = 0 then true else false
  have hx1_not_mem : x1 ∉ A := by
    simp [A, x1]
  have hshift_eq : shift x0 = shift x1 := by
    funext n
    simp [shift, x0, x1]
  have hx0_mem : x0 ∈ A := by
    simp [A, x0]
  have hx0_pre : x0 ∈ shift ⁻¹' B := by
    rw [hBdef]
    exact hx0_mem
  have hx1_pre : x1 ∈ shift ⁻¹' B := by
    simpa [Set.mem_preimage, hshift_eq] using hx0_pre
  have hx1_mem : x1 ∈ A := by
    rw [← hBdef]
    exact hx1_pre
  exact hx1_not_mem hx1_mem

/-
Remark 12.9 is a `bridge/view` item. Its owner abstractions are the Chapter 2 tail
`σ`-algebra `tailRandomVariableMeasurableSpace` and the Chapter 12 exchangeable
`σ`-algebra `exchangeableSigmaAlgebra`. The main public bridge theorem is the generic
process-level inclusion, and the coordinate-sequence-space statement is kept as its canonical
specialization.
-/
-- Proof sketch: a tail event for `X` depends only on coordinates from some index onward, hence is
-- unchanged by every finite permutation of coordinates. Therefore each tail stage belongs to the
-- corresponding finite-exchangeable stage, and intersecting over all stages gives the owner-level
-- inclusion into the exchangeable `σ`-algebra of the sample-sequence map.
/-- Helper for Remark 12.9: for any sequence of random variables `X`, the tail `σ`-algebra of `X`
is contained in the exchangeable `σ`-algebra of its sample-sequence map. -/
theorem tailRandomVariableMeasurableSpace_le_exchangeableSigmaAlgebra
    (X : ℕ → Ω → E) :
    tailRandomVariableMeasurableSpace X ≤ exchangeableSigmaAlgebra (Function.swap X) := by
  -- Rewrite both owner `σ`-algebras as intersections of their finite stages.
  rw [tailRandomVariableMeasurableSpace, tailMeasurableSpace_nat_eq_iInf_iSup_Ici,
    exchangeableSigmaAlgebra_eq_iInf_nExchangeableSigmaAlgebra]
  -- Each tail stage is fixed by every permutation of the discarded prefix.
  exact iInf_mono fun n ↦ tailStage_le_nExchangeableSigmaAlgebra X n

-- Proof sketch: for each `n`, every event depending only on coordinates `n, n + 1, ...` is
-- unchanged by permutations of the first `n` coordinates, so the `n`th tail stage lies in the
-- `n`th symmetric stage from Definition 12.6; intersect over `n`.
/-- Helper for Remark 12.9: on sequence space, the tail `σ`-algebra is contained in the
exchangeable `σ`-algebra. -/
theorem coordinateTailMeasurableSpace_le_exchangeableSequenceSigmaAlgebra :
    tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → E) → E) ≤
      exchangeableSequenceSigmaAlgebra := by
  simpa [exchangeableSigmaAlgebra, Function.swap] using
    tailRandomVariableMeasurableSpace_le_exchangeableSigmaAlgebra
      (Function.eval : ℕ → (ℕ → E) → E)

-- Proof sketch: on `Bool`-valued sequence space, the all-false event is measurable and invariant
-- under every finite permutation, so it belongs to the exchangeable `σ`-algebra; it is not tail
-- measurable because changing only the first coordinate leaves the tail fixed but destroys the
-- event.
/-- Remark 12.9 (2): for `Bool`-valued sequences, the inclusion of the tail `σ`-algebra into the
exchangeable `σ`-algebra can be strict. -/
theorem coordinateTailMeasurableSpace_lt_exchangeableSequenceSigmaAlgebra_bool :
    tailRandomVariableMeasurableSpace (Function.eval : ℕ → (ℕ → Bool) → Bool) <
      exchangeableSequenceSigmaAlgebra := by
  -- Route correction: use the all-false event as the separating witness, since it is obviously
  -- permutation-invariant and changing only the first coordinate destroys tail measurability.
  let A : Set (ℕ → Bool) := {x | ∀ n, x n = false}
  refine lt_of_le_of_ne coordinateTailMeasurableSpace_le_exchangeableSequenceSigmaAlgebra ?_
  intro hEq
  have hA_exchangeable : MeasurableSet[exchangeableSequenceSigmaAlgebra] A := by
    simpa [A] using allFalse_measurableSet_mem_exchangeableSequenceSigmaAlgebra
  have hA_tail :
      MeasurableSet[tailRandomVariableMeasurableSpace
        (Function.eval : ℕ → (ℕ → Bool) → Bool)] A := by
    rw [hEq]
    exact hA_exchangeable
  exact allFalse_not_measurableSet_tailRandomVariableMeasurableSpace_eval
    (by simpa [A] using hA_tail)

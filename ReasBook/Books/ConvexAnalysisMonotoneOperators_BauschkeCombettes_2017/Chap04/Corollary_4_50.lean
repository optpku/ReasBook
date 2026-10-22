/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_49
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_9

-- Declarations for this item will be appended below by the statement pipeline.

open Function Set

universe u

section

variable {H : Type u}

private theorem iInter_fixedPointSetOn_fin_succ (D : Set H) {n : ℕ}
    (T : Fin (n + 1) → H → H) :
    (⋂ i : Fin (n + 1), fixedPointSetOn D (T i)) =
      fixedPointSetOn D (T 0) ∩ ⋂ i : Fin n, fixedPointSetOn D (T i.succ) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_succ]

variable [NormedAddCommGroup H]

/-- Corollary 4.50: for a nonempty finite family `T 0, ..., T n` of strictly
quasinonexpansive self-maps of `D` with a common fixed point in `D`, the ordered composition is
strictly quasinonexpansive on `D`, and its fixed points in `D` are exactly the common fixed
points of the family. -/
theorem finiteComposition_strictlyQuasinonexpansiveOn_and_fixedPointSetOn_eq_iInter
    {n : ℕ} (D : Set H) (T : Fin (n + 1) → H → H)
    (hMaps : ∀ i, MapsTo (T i) D D)
    (hStrict : ∀ i, StrictlyQuasinonexpansiveOn D (T i))
    (hFix : (⋂ i, fixedPointSetOn D (T i)).Nonempty) :
    StrictlyQuasinonexpansiveOn D (finiteComposition T) ∧
      fixedPointSetOn D (finiteComposition T) = ⋂ i, fixedPointSetOn D (T i) := by
  induction n with
  | zero =>
      have hcomp : finiteComposition T = T 0 := by
        funext x
        rfl
      have hiInter : (⋂ i : Fin 1, fixedPointSetOn D (T i)) = fixedPointSetOn D (T 0) := by
        ext x
        simp [Set.mem_iInter]
      constructor
      · simpa [hcomp] using hStrict 0
      · simpa [hcomp] using hiInter.symm
  | succ n ih =>
      have hFix' :
          (fixedPointSetOn D (T 0) ∩ ⋂ i : Fin (n + 1), fixedPointSetOn D (T i.succ)).Nonempty := by
        simpa [iInter_fixedPointSetOn_fin_succ D T] using hFix
      rcases hFix' with ⟨y, hy0, hytail⟩
      have htailMaps : ∀ i : Fin (n + 1), MapsTo (T i.succ) D D := fun i ↦ hMaps i.succ
      have htailStrict :
          ∀ i : Fin (n + 1), StrictlyQuasinonexpansiveOn D (T i.succ) := fun i ↦ hStrict i.succ
      have htailFix : (⋂ i : Fin (n + 1), fixedPointSetOn D (T i.succ)).Nonempty := ⟨y, hytail⟩
      have htail :=
        ih (fun i : Fin (n + 1) ↦ T i.succ) htailMaps htailStrict htailFix
      have htailMapsTo : MapsTo (finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) D D :=
        finiteComposition_mapsTo D (fun i : Fin (n + 1) ↦ T i.succ) htailMaps
      have hpairFix :
          (fixedPointSetOn D (T 0) ∩
              fixedPointSetOn D (finiteComposition (fun i : Fin (n + 1) ↦ T i.succ))).Nonempty := by
        refine ⟨y, hy0, ?_⟩
        rw [htail.2]
        exact hytail
      have hT0_qne : QuasinonexpansiveOn D (T 0) :=
        StrictlyQuasinonexpansiveOn.quasinonexpansiveOn (hStrict 0)
      have htail_qne :
          QuasinonexpansiveOn D (finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) :=
        StrictlyQuasinonexpansiveOn.quasinonexpansiveOn htail.1
      have hpairStrict :
          StrictlyQuasinonexpansiveOn D
            (T 0 ∘ finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) :=
        (strictlyQuasinonexpansiveOn_comp
          (hMaps 0) htailMapsTo hpairFix (hStrict 0) htail.1).2
      have hpairFixed :
          fixedPointSetOn D (T 0 ∘ finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) =
            fixedPointSetOn D (T 0) ∩
              fixedPointSetOn D (finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) :=
        fixedPointSetOn_comp_eq_inter_of_one_strictlyQuasinonexpansive
          (hMaps 0) htailMapsTo hT0_qne htail_qne hpairFix (.inl (hStrict 0))
      constructor
      · simpa [finiteComposition_succ] using hpairStrict
      · calc
          fixedPointSetOn D (finiteComposition T)
              = fixedPointSetOn D (T 0 ∘ finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) := by
                  rw [finiteComposition_succ]
          _ = fixedPointSetOn D (T 0) ∩
                fixedPointSetOn D (finiteComposition (fun i : Fin (n + 1) ↦ T i.succ)) :=
              hpairFixed
          _ = fixedPointSetOn D (T 0) ∩
                ⋂ i : Fin (n + 1), fixedPointSetOn D (T i.succ) := by
              rw [htail.2]
          _ = ⋂ i : Fin (n + 2), fixedPointSetOn D (T i) := by
              exact (iInter_fixedPointSetOn_fin_succ D T).symm

end

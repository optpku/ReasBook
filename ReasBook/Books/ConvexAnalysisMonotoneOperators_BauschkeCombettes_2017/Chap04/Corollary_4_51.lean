/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Corollary_4_50
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Remark_4_36

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Function Set

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H}

private noncomputable def ambientSelfMap (T : D → D) : H → H :=
  fun x ↦ by
    classical
    exact if hx : x ∈ D then (T ⟨x, hx⟩ : H) else x

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private lemma ambientSelfMap_apply (T : D → D) {x : H} (hx : x ∈ D) :
    ambientSelfMap T x = T ⟨x, hx⟩ := by
  classical
  simp [ambientSelfMap, hx]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private lemma ambientSelfMap_mapsTo {T : D → D} :
    MapsTo (ambientSelfMap T) D D := by
  intro x hx
  rw [ambientSelfMap_apply T hx]
  exact (T ⟨x, hx⟩).property

private lemma ambientSelfMap_strictlyQuasinonexpansiveOn_of_averagedWith
    {T : D → D}
    (havg : ∃ α, AveragedWith α (fun x : D ↦ (T x : H))) :
    StrictlyQuasinonexpansiveOn D (ambientSelfMap T) := by
  rcases havg with ⟨α, havg⟩
  rcases averagedWith_iff.mp havg with ⟨hα, R, hR, hTR⟩
  have havg' : AveragedWith α (fun x : D ↦ ambientSelfMap T x) := by
    refine averagedWith_iff.mpr ?_
    refine ⟨hα, R, hR, ?_⟩
    ext x
    simpa [ambientSelfMap, dif_pos x.property] using congrArg (fun f : D → H ↦ f x) hTR
  exact averaged_strictlyQuasinonexpansiveOn havg'

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
private lemma finiteComposition_ambientSelfMap_apply :
    ∀ {m : ℕ} (T : Fin m → D → D) (x : D),
      finiteComposition (fun i ↦ ambientSelfMap (T i)) x = finiteComposition T x
  | 0, _, _ => rfl
  | _ + 1, T, x => by
      rw [finiteComposition_succ, finiteComposition_succ]
      change
        ambientSelfMap (T 0) (finiteComposition (fun i ↦ ambientSelfMap (T i.succ)) x) =
          T 0 (finiteComposition (fun i ↦ T i.succ) x)
      rw [finiteComposition_ambientSelfMap_apply (fun i ↦ T i.succ) x]
      simpa using ambientSelfMap_apply (T 0) (finiteComposition (fun i ↦ T i.succ) x).property

-- Proof sketch: each averaged self-map on the subtype `D` yields, by ambient extension on `H`,
-- a strictly quasinonexpansive self-map of `D`; Corollary 4.50 then identifies the fixed points
-- of the ambient finite composition with the intersection of the individual fixed-point sets, and
-- restricting back to the subtype gives the stated fixed-point identity.
/-- Corollary 4.51: for a finite family of averaged self-maps of `D` with a common fixed point,
the fixed points of their ordered composition are exactly the common fixed points. -/
theorem fixedPoints_finiteComposition_eq_iInter_fixedPoints_of_averagedWith
    {m : ℕ} (T : Fin m → D → D)
    (havg : ∀ i, ∃ α, AveragedWith α (fun x : D ↦ (T i x : H)))
    (hfix : Set.Nonempty (⋂ i, Function.fixedPoints (T i) : Set D)) :
    Function.fixedPoints (finiteComposition T) = ⋂ i, Function.fixedPoints (T i) := by
  cases m with
  | zero =>
      ext x
      simp [finiteComposition]
  | succ n =>
      let S : Fin (n + 1) → H → H := fun i ↦ ambientSelfMap (T i)
      have hMaps : ∀ i, MapsTo (S i) D D := by
        intro i
        exact ambientSelfMap_mapsTo
      have hStrict : ∀ i, StrictlyQuasinonexpansiveOn D (S i) := by
        intro i
        exact ambientSelfMap_strictlyQuasinonexpansiveOn_of_averagedWith (havg i)
      have hFix : (⋂ i, fixedPointSetOn D (S i)).Nonempty := by
        rcases hfix with ⟨x, hx⟩
        refine ⟨(x : H), ?_⟩
        rw [Set.mem_iInter] at hx ⊢
        intro i
        rw [mem_fixedPointSetOn_iff]
        constructor
        · exact x.property
        · have hxi : T i x = x := Function.mem_fixedPoints_iff.mp (hx i)
          simpa [S, ambientSelfMap_apply (T i) x.property] using congrArg Subtype.val hxi
      have hComp :=
        finiteComposition_strictlyQuasinonexpansiveOn_and_fixedPointSetOn_eq_iInter
          D S hMaps hStrict hFix
      ext x
      have hcomp :
          x ∈ Function.fixedPoints (finiteComposition T) ↔
            (x : H) ∈ fixedPointSetOn D (finiteComposition S) := by
        rw [Function.mem_fixedPoints_iff, mem_fixedPointSetOn_iff]
        constructor
        · intro hx
          constructor
          · exact x.property
          · simpa [S, finiteComposition_ambientSelfMap_apply T x] using congrArg Subtype.val hx
        · rintro ⟨_, hx⟩
          apply Subtype.ext
          simpa [S, finiteComposition_ambientSelfMap_apply T x] using hx
      have hiInter :
          x ∈ (⋂ i, Function.fixedPoints (T i) : Set D) ↔
            (x : H) ∈ ⋂ i, fixedPointSetOn D (S i) := by
        rw [Set.mem_iInter, Set.mem_iInter]
        constructor
        · intro hx i
          rw [mem_fixedPointSetOn_iff]
          constructor
          · exact x.property
          · have hxi : T i x = x := Function.mem_fixedPoints_iff.mp (hx i)
            simpa [S, ambientSelfMap_apply (T i) x.property] using congrArg Subtype.val hxi
        · intro hx i
          rw [Function.mem_fixedPoints_iff]
          rcases (mem_fixedPointSetOn_iff.mp (hx i)) with ⟨_, hxi⟩
          apply Subtype.ext
          simpa [S, ambientSelfMap_apply (T i) x.property] using hxi
      exact hcomp.trans <| by
        rw [hComp.2]
        exact hiInter.symm

end

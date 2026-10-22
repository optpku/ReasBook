/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part1

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- Helper for Text 26.4.0.2: any actual witness of the target conclusion already rules out the
degenerate specialization `n = 0` and `C = ∅`, because that specialization is exactly where the
singleton-space interior-domain contradiction applies. -/
lemma helperForText_26_4_0_2_localWitness_excludes_finZero_empty
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hWitness :
      ∃ F : (Fin n → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ C, F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    ¬ (n = 0 ∧ C = (∅ : Set (Fin n → ℝ))) := by
  rintro ⟨hn, hCempty⟩
  -- First specialize the ambient dimension to the singleton space `Fin 0 → ℝ`.
  subst n
  -- Then specialize the source set to `∅`, where the stored witness becomes impossible.
  subst C
  exact helperForText_26_4_0_2_emptyConclusionImpossible_finZero (f := f) L hWitness

/-- Helper for Text 26.4.0.2: once the local parameters are specialized to `n = 0` and
`C = ∅`, the exact local existential conclusion of the target theorem is impossible. This
packages the bad case as a direct obstruction for the eventual theorem-level case split. -/
lemma helperForText_26_4_0_2_localGoalFalse_of_finZero_empty
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hBadSpecialization : n = 0 ∧ C = (∅ : Set (Fin n → ℝ))) :
    ¬ (∃ F : (Fin n → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
      LowerSemicontinuous F ∧
      (∀ x ∈ C, F x = (f x : EReal)) ∧
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
      ∀ xStar : legendreGradientImage
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
        (L.conjFun xStar : EReal) =
          fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  intro hWitness
  -- Any witness would already force the negation of the degenerate specialization.
  exact
    (helperForText_26_4_0_2_localWitness_excludes_finZero_empty (f := f) L hWitness)
      hBadSpecialization

/-- Helper for Text 26.4.0.2: in zero dimension, any actual witness for the target conclusion
forces the source set to be nonempty, so the repaired theorem statement must exclude the empty
source specialization when `n = 0`. -/
lemma helperForText_26_4_0_2_localWitness_forces_nonemptySource_finZero
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hn : n = 0)
    (hWitness :
      ∃ F : (Fin n → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ C, F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    C ≠ (∅ : Set (Fin n → ℝ)) := by
  intro hCempty
  -- The previously isolated bad specialization immediately contradicts any such witness.
  exact
    (helperForText_26_4_0_2_localGoalFalse_of_finZero_empty (f := f) L ⟨hn, hCempty⟩)
      hWitness

/-- Helper for Text 26.4.0.2: in dimension zero, any actual witness of the target conclusion
forces the source set to contain a point. This isolates the concrete side condition missing from
the current false theorem header. -/
lemma helperForText_26_4_0_2_localWitness_nonempty_of_finZero
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hWitness :
      ∃ F : (Fin n → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ C, F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    n = 0 → C.Nonempty := by
  intro hn
  -- The previously proved zero-dimensional obstruction already rules out `C = ∅`.
  have hCne :
      C ≠ (∅ : Set (Fin n → ℝ)) :=
    helperForText_26_4_0_2_localWitness_forces_nonemptySource_finZero (f := f) L hn hWitness
  classical
  by_contra hC_nonempty
  -- Turning `¬ C.Nonempty` into `C = ∅` identifies the exact forbidden specialization.
  have hCempty : C = (∅ : Set (Fin n → ℝ)) := by
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro x hx
    exact hC_nonempty ⟨x, hx⟩
  exact hCne hCempty

/-- Helper for Text 26.4.0.2: any actual witness of the target conclusion forces the concrete
zero-dimensional side condition `n ≠ 0 ∨ C.Nonempty`. This packages the exact local repair that
the obstruction chain isolates. -/
lemma helperForText_26_4_0_2_localWitness_forces_repairedSideCondition
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hWitness :
      ∃ F : (Fin n → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ C, F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate n F (xStar.1 : Fin n → ℝ)) :
    n ≠ 0 ∨ C.Nonempty := by
  by_cases hn : n = 0
  · -- In zero dimension the obstruction helper already produces an explicit point of `C`.
    exact Or.inr (helperForText_26_4_0_2_localWitness_nonempty_of_finZero (f := f) L hWitness hn)
  · -- Away from zero dimension the repaired side condition reduces to `n ≠ 0`.
    exact Or.inl hn

/-- Helper for Text 26.4.0.2: failing the repaired side condition `n ≠ 0 ∨ C.Nonempty` is
exactly the bad specialization `n = 0` and `C = ∅` isolated by the obstruction chain. -/
lemma helperForText_26_4_0_2_not_repairedSideCondition_iff_badSpecialization
    {n : ℕ} {C : Set (Fin n → ℝ)} :
    ¬ (n ≠ 0 ∨ C.Nonempty) ↔ n = 0 ∧ C = (∅ : Set (Fin n → ℝ)) := by
  constructor
  · intro hNoRepair
    -- First `n ≠ 0` is impossible, so the ambient dimension must be zero.
    have hn : n = 0 := by
      by_cases hn : n = 0
      · exact hn
      · exact False.elim (hNoRepair (Or.inl hn))
    -- Then `C.Nonempty` is impossible as well, so `C` must be empty.
    have hCempty : C = (∅ : Set (Fin n → ℝ)) := by
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      intro x hx
      exact hNoRepair (Or.inr ⟨x, hx⟩)
    exact ⟨hn, hCempty⟩
  · rintro ⟨hn, hCempty⟩ hRepair
    -- Unpack the repaired side condition and show that each branch contradicts the bad case.
    rcases hRepair with hn_ne | hC_nonempty
    · exact hn_ne hn
    · rcases hC_nonempty with ⟨x, hxC⟩
      rw [hCempty] at hxC
      exact hxC.elim

/-- Helper for Text 26.4.0.2: if the repaired side condition `n ≠ 0 ∨ C.Nonempty` fails, then
the exact local existential conclusion of the target theorem is impossible. -/
lemma helperForText_26_4_0_2_localGoalFalse_of_not_repairedSideCondition
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hNoRepair : ¬ (n ≠ 0 ∨ C.Nonempty)) :
    ¬ (∃ F : (Fin n → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
      LowerSemicontinuous F ∧
      (∀ x ∈ C, F x = (f x : EReal)) ∧
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
      ∀ xStar : legendreGradientImage
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
        (L.conjFun xStar : EReal) =
          fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  -- Translate failure of the repaired side condition into the concrete bad specialization.
  have hBadSpecialization : n = 0 ∧ C = (∅ : Set (Fin n → ℝ)) :=
    (helperForText_26_4_0_2_not_repairedSideCondition_iff_badSpecialization
      (n := n) (C := C)).1 hNoRepair
  -- The bad specialization is exactly the one already ruled out by the local obstruction.
  exact helperForText_26_4_0_2_localGoalFalse_of_finZero_empty (f := f) L hBadSpecialization

/-- Helper for Text 26.4.0.2: if the repaired side condition `n ≠ 0 ∨ C.Nonempty` fails, then
the exact local existential goal type is empty. -/
lemma helperForText_26_4_0_2_localGoalIsEmpty_of_not_repairedSideCondition
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hNoRepair : ¬ (n ≠ 0 ∨ C.Nonempty)) :
    IsEmpty
      (∃ F : (Fin n → ℝ) → EReal,
        ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        (∀ x ∈ C, F x = (f x : EReal)) ∧
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
        ∀ xStar : legendreGradientImage
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          (L.conjFun xStar : EReal) =
            fenchelConjugate n F (xStar.1 : Fin n → ℝ)) := by
  refine ⟨?_⟩
  intro hWitness
  -- Reuse the previous helper, now packaged as an `IsEmpty` statement for the exact goal type.
  exact
    helperForText_26_4_0_2_localGoalFalse_of_not_repairedSideCondition
      (f := f) L hNoRepair hWitness

/-- Helper for Text 26.4.0.2: the local obstruction splits into a reusable summary. The
declaration-form universal source type is already empty, any actual local witness forces the
repaired side condition `n ≠ 0 ∨ C.Nonempty`, and failing that side condition empties the exact
local existential goal. -/
lemma helperForText_26_4_0_2_localObstructionSummary
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    IsEmpty
      (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
        (_hC_convex : Convex ℝ C) (_hf_convex : ConvexOn ℝ C f)
        (L' : LegendreTransformationOn
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))),
          ∃ F : (Fin n → ℝ) → EReal,
            ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
            LowerSemicontinuous F ∧
            (∀ x ∈ C, F x = (f x : EReal)) ∧
            interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
            ∀ xStar : legendreGradientImage
                ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
              (L'.conjFun xStar : EReal) =
                fenchelConjugate n F (xStar.1 : Fin n → ℝ)) ∧
      (((∃ F : (Fin n → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ C, F x = (f x : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
              (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate n F (xStar.1 : Fin n → ℝ)) →
          n ≠ 0 ∨ C.Nonempty) ∧
        (¬ (n ≠ 0 ∨ C.Nonempty) →
          IsEmpty
            (∃ F : (Fin n → ℝ) → EReal,
              ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
              LowerSemicontinuous F ∧
              (∀ x ∈ C, F x = (f x : EReal)) ∧
              interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
              ∀ xStar : legendreGradientImage
                  ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
                  (fun x : EuclideanSpace ℝ (Fin n) =>
                    f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
                (L.conjFun xStar : EReal) =
                  fenchelConjugate n F (xStar.1 : Fin n → ℝ)))) := by
  -- Reuse the existing reduction helper for the empty declaration-form source type.
  refine ⟨(helperForText_26_4_0_2_localReductionRouteData hC_convex hf_convex L).1, ?_⟩
  constructor
  · -- Any actual local witness already rules out the degenerate `n = 0`, `C = ∅` case.
    exact helperForText_26_4_0_2_localWitness_forces_repairedSideCondition (f := f) L
  · -- Failing the repaired side condition packages the local goal itself as an empty type.
    exact helperForText_26_4_0_2_localGoalIsEmpty_of_not_repairedSideCondition (f := f) L

/-- Helper for Text 26.4.0.2: the current theorem hypotheses do not by themselves force the
repaired side condition `n ≠ 0 ∨ C.Nonempty`; the bad specialization `n = 0`, `C = ∅`,
`f = 0` still satisfies them. -/
lemma helperForText_26_4_0_2_hypotheses_doNotForce_repairedSideCondition :
    ¬ (∀ {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ},
        Convex ℝ C →
        ConvexOn ℝ C f →
        ∀ L : LegendreTransformationOn
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
            (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
          n ≠ 0 ∨ C.Nonempty) := by
  intro hForce
  let f0 : (Fin 0 → ℝ) → ℝ := fun _ => 0
  -- The existing counterexample helper supplies convexity and a Legendre datum in the bad case.
  rcases helperForText_26_4_0_2_counterexampleHypotheses_finZero (f := f0) with
    ⟨hC_convex, hf_convex, hLegendre⟩
  rcases hLegendre with ⟨L⟩
  -- Specializing the alleged implication to `n = 0`, `C = ∅`, `f = 0` yields the impossible
  -- repaired side condition for the empty zero-dimensional source.
  have hRepair :
      (0 : ℕ) ≠ 0 ∨ (∅ : Set (Fin 0 → ℝ)).Nonempty :=
    hForce (n := 0) (C := (∅ : Set (Fin 0 → ℝ))) (f := f0) hC_convex hf_convex L
  rcases hRepair with hZeroNe | hC_nonempty
  · exact hZeroNe rfl
  · rcases hC_nonempty with ⟨x, hx⟩
    simpa using hx

/-- Helper for Text 26.4.0.2: under the current unrepaired theorem header, the exact local
existential goal has only one formal alternative. Either the repaired side condition
`n ≠ 0 ∨ C.Nonempty` holds, or the obstruction chain already packages the local goal type as
empty. -/
lemma helperForText_26_4_0_2_localGoalIsEmpty_or_repairedSideCondition
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    IsEmpty
        (∃ F : (Fin n → ℝ) → EReal,
          ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
          LowerSemicontinuous F ∧
          (∀ x ∈ C, F x = (f x : EReal)) ∧
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
          ∀ xStar : legendreGradientImage
              ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
              (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
            (L.conjFun xStar : EReal) =
              fenchelConjugate n F (xStar.1 : Fin n → ℝ)) ∨
      (n ≠ 0 ∨ C.Nonempty) := by
  classical
  by_cases hRepair : n ≠ 0 ∨ C.Nonempty
  · -- When the repaired side condition already holds, the local alternative is immediate.
    exact Or.inr hRepair
  · -- Otherwise the obstruction summary identifies the exact local goal type as empty.
    exact
      Or.inl
        ((helperForText_26_4_0_2_localObstructionSummary hC_convex hf_convex (f := f) L).2.2
          hRepair)

/-- Helper for Text 26.4.0.2: transport the openness and differentiability data carried by the
Legendre package from the Euclidean-space coordinates back to the textbook coordinates
`Fin n → ℝ`. -/
lemma helperForText_26_4_0_2_openAndDifferentiableOn_of_legendreDatum
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x))) :
    IsOpen C ∧ DifferentiableOn ℝ f C := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (Fin n) ℝ
  let toEuclid : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp (p := 2) x
  have hsource :
      toEuclid '' C = e ⁻¹' C := by
    -- The source set of `L` is exactly the preimage of `C` under the coordinate equivalence.
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [e, toEuclid] using hy
    · intro hx
      refine ⟨e x, hx, ?_⟩
      rfl
  have himage :
      e '' (toEuclid '' C) = C := by
    -- Applying the coordinate equivalence to that source set recovers the original `C`.
    ext y
    constructor
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      simpa [e, toEuclid] using hz
    · intro hy
      exact ⟨toEuclid y, ⟨y, hy, rfl⟩, by rfl⟩
  have hopenImage : IsOpen (e '' (toEuclid '' C)) := by
    -- Open sets are preserved by the continuous linear equivalence `e`.
    exact e.isOpenMap _ (by simpa [e, toEuclid] using L.isOpen_source)
  have hopenC : IsOpen C := by
    simpa [himage] using hopenImage
  have hdiffComp :
      DifferentiableOn ℝ (fun x : EuclideanSpace ℝ (Fin n) => f (e x)) (e ⁻¹' C) := by
    -- The domain stored in `L` is the same preimage set after unpacking the Euclidean coercions.
    simpa [hsource, e, toEuclid] using L.differentiableOn_source
  have hdiff : DifferentiableOn ℝ f C := by
    -- Compose with the inverse coordinate equivalence to recover differentiability of `f` on `C`.
    simpa [Function.comp, e] using
      (ContinuousLinearEquiv.comp_right_differentiableOn_iff (iso := e) (f := f) (s := C)).1
        hdiffComp
  exact ⟨hopenC, hdiff⟩

/-- Helper for Text 26.4.0.2: a proper convex function on all of `ℝⁿ` can be repackaged as a
proper convex `EReal`-valued function in the Jensen-style sense used locally in Section 26. -/
lemma helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    ProperConvexERealFunction (F := (Fin n → ℝ)) f := by
  constructor
  · constructor
    · -- The Chapter 25 notion already excludes the value `⊥` everywhere on `univ`.
      intro x
      exact hproper.2.2 x (by simp)
    · -- Nonempty epigraph gives a point where the function is finite.
      rcases
          (nonempty_epigraph_iff_nonempty_effectiveDomain
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f)).1 hproper.2.1 with
        ⟨x, hx⟩
      exact
        ⟨x,
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hx⟩
  · have hnotbot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
      intro x
      exact hproper.2.2 x (by simp)
    have hjensen :=
      (convexFunctionOn_univ_iff_jensen_inequality (f := f) hnotbot).1 hproper.1
    intro x y a b ha hb hab
    let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
    let z : Fin 2 → (Fin n → ℝ) := fun i => if i = 0 then x else y
    have hw : ∀ i : Fin 2, 0 ≤ w i := by
      intro i
      fin_cases i <;> simp [w, ha, hb]
    have hsum : (∑ i : Fin 2, w i) = 1 := by
      simp [w, Fin.sum_univ_two, hab]
    have htwo := hjensen 2 w z hw hsum
    -- Specializing the Jensen inequality to two points yields the Section 26 convexity form.
    simpa [w, z, Fin.sum_univ_two, add_comm, add_left_comm, add_assoc] using htwo

/-- Helper for Text 26.4.0.2: in positive dimension, the singleton `{0}` has empty interior. -/
lemma helperForText_26_4_0_2_singletonInterior_empty_of_ne_zero
    {n : ℕ} (hn : n ≠ 0) :
    interior ({0} : Set (Fin n → ℝ)) = (∅ : Set (Fin n → ℝ)) := by
  haveI : NeZero n := ⟨hn⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hnonempty : (interior ({0} : Set (Fin n → ℝ))).Nonempty := ⟨x, hx⟩
  have hconv : Convex ℝ ({0} : Set (Fin n → ℝ)) := by
    simp
  have htop : affineSpan ℝ ({0} : Set (Fin n → ℝ)) = ⊤ :=
    (Convex.interior_nonempty_iff_affineSpan_eq_top hconv).1 hnonempty
  have hmemTop : (1 : Fin n → ℝ) ∈ affineSpan ℝ ({0} : Set (Fin n → ℝ)) := by
    simpa [htop]
  have hone : (1 : Fin n → ℝ) = (0 : Fin n → ℝ) :=
    (AffineSubspace.mem_affineSpan_singleton ℝ (Fin n → ℝ)).1 hmemTop
  -- In a nontrivial ambient space, the constant functions `0` and `1` cannot coincide.
  exact one_ne_zero hone

/-- Helper for Text 26.4.0.2: when `C = ∅` but `n ≠ 0`, the indicator of `{0}` gives an explicit
closed proper convex witness whose effective-domain interior is empty. -/
lemma helperForText_26_4_0_2_indicatorSingletonPackage_of_emptySource
    {n : ℕ} (hn : n ≠ 0) :
    ProperConvexERealFunction (F := (Fin n → ℝ))
        (indicatorFunction ({0} : Set (Fin n → ℝ))) ∧
      LowerSemicontinuous (indicatorFunction ({0} : Set (Fin n → ℝ))) ∧
      interior
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (indicatorFunction ({0} : Set (Fin n → ℝ)))) = ∅ := by
  have hproperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (indicatorFunction ({0} : Set (Fin n → ℝ))) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty (by simp) (by simp)
  have hproper :
      ProperConvexERealFunction (F := (Fin n → ℝ))
        (indicatorFunction ({0} : Set (Fin n → ℝ))) := by
    -- Repackage the standard proper-convex-on-`univ` witness into the Section 26 predicate.
    exact
      helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn hproperOn
  have hls : LowerSemicontinuous (indicatorFunction ({0} : Set (Fin n → ℝ))) := by
    have hclosed :=
      closedConvexFunction_indicator_neg (n := n) (C := ({0} : Set (Fin n → ℝ)))
        (by simp) (by simp) (by simp)
    -- The negation of `{0}` is again `{0}`, so the standard closed-indicator theorem applies.
    simpa using hclosed.1.2
  have hInterior :
      interior
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (indicatorFunction ({0} : Set (Fin n → ℝ)))) = ∅ := by
    simpa [effectiveDomain_indicatorFunction_eq] using
      helperForText_26_4_0_2_singletonInterior_empty_of_ne_zero (n := n) hn
  exact ⟨hproper, hls, hInterior⟩

/-- Helper for Text 26.4.0.2: transporting the Euclidean-space source function
`z ↦ f ((EuclideanSpace.equiv (Fin n) ℝ) z)` back to textbook coordinates sends its gradient at
`(EuclideanSpace.equiv (Fin n) ℝ).symm x` to the Fréchet derivative determined by the transported
coordinate gradient. -/
lemma helperForText_26_4_0_2_sourceGradient_transport_fderiv_form
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hdiffAt : DifferentiableAt ℝ f x) :
    HasFDerivAt
      (fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z))
      ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm (euclideanGradientAt f x)))
      ((EuclideanSpace.equiv (Fin n) ℝ).symm x) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hf :
      HasFDerivAt f
        (helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x)) x :=
    helperForCorollary_25_5_1_hasFDerivAt_dotProductContinuousLinearMap hdiffAt
  have hcomp :
      HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => f (e z))
        ((helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x)).comp
          e.toContinuousLinearMap)
        (e.symm x) := by
    -- Compose the coordinate-space derivative of `f` with the Euclidean-coordinate equivalence.
    simpa using hf.comp (e.symm x) e.hasFDerivAt
  have hmap :
      ((helperForCorollary_25_5_1_dotProductContinuousLinearMap (euclideanGradientAt f x)).comp
        e.toContinuousLinearMap) =
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
          (e.symm (euclideanGradientAt f x))) := by
    -- Evaluate both continuous linear maps on an arbitrary test vector and compare pairings.
    ext z
    change (euclideanGradientAt f x) ⬝ᵥ ((EuclideanSpace.equiv (Fin n) ℝ) z) =
      inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm (euclideanGradientAt f x)) z
    rw [show (EuclideanSpace.equiv (Fin n) ℝ) z = z.ofLp by rfl]
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  -- The composed derivative is exactly the inner-product functional of the transported gradient.
  simpa [e, hmap] using hcomp

/-- Helper for Text 26.4.0.2: transporting the Euclidean-space source function
`z ↦ f ((EuclideanSpace.equiv (Fin n) ℝ) z)` back to textbook coordinates sends its gradient at
`(EuclideanSpace.equiv (Fin n) ℝ).symm x` to the coordinate gradient `euclideanGradientAt f x`. -/
lemma helperForText_26_4_0_2_sourceGradient_transport
    {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ}
    (hdiffAt : DifferentiableAt ℝ f x) :
    ((gradient
        (fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z))
        ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) =
      euclideanGradientAt f x := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hfderiv :
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) => f (e z))
        ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
          (e.symm (euclideanGradientAt f x)))
        (e.symm x) := by
    -- First transport the Fréchet derivative, which avoids a heavier gradient conversion.
    exact helperForText_26_4_0_2_sourceGradient_transport_fderiv_form (f := f) (x := x) hdiffAt
  have hgradAt :
      HasGradientAt
        (fun z : EuclideanSpace ℝ (Fin n) => f (e z))
        (e.symm (euclideanGradientAt f x))
        (e.symm x) :=
    (hasGradientAt_iff_hasFDerivAt).2 hfderiv
  have hgrad :
      gradient (fun z : EuclideanSpace ℝ (Fin n) => f (e z)) (e.symm x) =
        e.symm (euclideanGradientAt f x) := hgradAt.gradient
  -- Coercing the Euclidean-space gradient back to coordinates yields the target identity.
  exact
    congrArg
      (fun z : EuclideanSpace ℝ (Fin n) => ((z : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)) hgrad

/-- Helper for Text 26.4.0.2: the closed extension
`F = convexFunctionClosure (fun x => (f x : EReal) + indicatorFunction C x)` has
`euclideanGradientAt f x` as a Euclidean subgradient at every `x ∈ C`. -/
lemma helperForText_26_4_0_2_closedExtension_subgradient_at_coordinateGradient
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hf_diff : DifferentiableOn ℝ f C)
    {fExt : (Fin n → ℝ) → EReal} (hfExt : fExt = fun y => (f y : EReal) + indicatorFunction C y)
    {F : (Fin n → ℝ) → EReal} (hF : F = convexFunctionClosure fExt)
    (hproperExtOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fExt)
    {x : Fin n → ℝ} (hx : x ∈ C) :
    IsEuclideanSubgradientAt F x (euclideanGradientAt f x) := by
  have hdiffAt : DifferentiableAt ℝ f x :=
    (hf_diff x hx).differentiableAt (hC_open.mem_nhds hx)
  rcases
      helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := hC_open) (f := f) (x := x) hx hdiffAt with
    ⟨hExtDiffRaw, hExtGradRaw⟩
  have hsubneExt : Set.Nonempty (subdifferentialAt fExt x) := by
    have hpreimageRaw :
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
            subdifferentialAt (fun y => (f y : EReal) + indicatorFunction C y) x) =
          ({erealGradientAt hExtDiffRaw} : Set (Fin n → ℝ)) := by
      have hfExtConvRaw : ConvexFunction (fun y => (f y : EReal) + indicatorFunction C y) := by
        simpa [hfExt, ConvexFunction] using hproperExtOn.1
      exact
        helperForTheorem_25_7_subdifferentialPreimage_eq_singleton_gradient
          hfExtConvRaw hExtDiffRaw
    refine ⟨dotProductEquiv ℝ (Fin n) (erealGradientAt hExtDiffRaw), ?_⟩
    change erealGradientAt hExtDiffRaw ∈
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt fExt x)
    rw [show ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt fExt x) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (fun y => (f y : EReal) + indicatorFunction C y) x) by
        simp [hfExt]]
    simpa [hpreimageRaw]
  have hclosure :=
    convexFunctionClosure_eq_at_subdifferentiable_point_and_subdifferential_eq
      fExt hproperExtOn x hsubneExt
  have hsubExt : IsEuclideanSubgradientAt fExt x (euclideanGradientAt f x) := by
    have hpreimageRaw :
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
            subdifferentialAt (fun y => (f y : EReal) + indicatorFunction C y) x) =
          ({erealGradientAt hExtDiffRaw} : Set (Fin n → ℝ)) := by
      have hfExtConvRaw : ConvexFunction (fun y => (f y : EReal) + indicatorFunction C y) := by
        simpa [hfExt, ConvexFunction] using hproperExtOn.1
      exact
        helperForTheorem_25_7_subdifferentialPreimage_eq_singleton_gradient
          hfExtConvRaw hExtDiffRaw
    change euclideanGradientAt f x ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt fExt x)
    rw [show ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt fExt x) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (fun y => (f y : EReal) + indicatorFunction C y) x) by
        simp [hfExt]]
    rw [hpreimageRaw]
    exact hExtGradRaw.symm
  have hsubF : IsEuclideanSubgradientAt F x (euclideanGradientAt f x) := by
    rw [hF]
    change dotProductEquiv ℝ (Fin n) (euclideanGradientAt f x) ∈
      subdifferentialAt (convexFunctionClosure fExt) x
    rw [hclosure.2]
    simpa [IsEuclideanSubgradientAt] using hsubExt
  exact hsubF

/-- Helper for Text 26.4.0.2: at each `x ∈ C`, the closed extension
`F = convexFunctionClosure (fun x => (f x : EReal) + indicatorFunction C x)` satisfies the
Fenchel-Young equality in the subtraction form used later in the theorem. -/
lemma helperForText_26_4_0_2_fenchelYoung_subtractionForm
    {n : ℕ} {F : (Fin n → ℝ) → EReal} {x xStar : Fin n → ℝ}
    (hproperFOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F)
    (hFY : FenchelYoungEqualityAt F x xStar) :
    fenchelConjugate n F xStar = (((dotProduct x xStar : ℝ) : EReal) - F x) := by
  have hFiniteF :=
    helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality F hproperFOn x xStar (le_of_eq hFY)
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
    proper_fenchelConjugate_of_proper (n := n) (f := F) hproperFOn
  have hStar_ne_bot : fenchelConjugate n F xStar ≠ (⊥ : EReal) :=
    hproperStar.2.2 xStar (by simp)
  have hStar_ne_top : fenchelConjugate n F xStar ≠ (⊤ : EReal) := by
    intro htop
    rw [FenchelYoungEqualityAt] at hFY
    have hleft_top : F x + fenchelConjugate n F xStar = (⊤ : EReal) := by
      -- A finite primal value cannot compensate for a conjugate value equal to `⊤`.
      simpa [htop] using (EReal.add_top_of_ne_bot hFiniteF.2)
    exact EReal.coe_ne_top (dotProduct x xStar) (hFY.symm.trans hleft_top)
  have hFYReal :
      (F x).toReal + (fenchelConjugate n F xStar).toReal = dotProduct x xStar := by
    -- Convert the finite Fenchel-Young equality to an equality of real numbers.
    rw [FenchelYoungEqualityAt] at hFY
    rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hFiniteF.1) (hBot := hFiniteF.2)] at hFY
    rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hStar_ne_top) (hBot := hStar_ne_bot)] at hFY
    exact_mod_cast hFY
  have hSubReal :
      (fenchelConjugate n F xStar).toReal = dotProduct x xStar - (F x).toReal := by
    -- Rearranging the real equality isolates the conjugate value.
    linarith
  have hright :
      (((dotProduct x xStar : ℝ) : EReal) - F x) =
        (((dotProduct x xStar - (F x).toReal : ℝ) : EReal)) := by
    -- The right-hand side is finite because `F x` is finite under Fenchel-Young equality.
    rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
          (hTop := hFiniteF.1) (hBot := hFiniteF.2)]
    simp [EReal.coe_sub]
  rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
        (hTop := hStar_ne_top) (hBot := hStar_ne_bot)]
  rw [hright]
  -- Cast the real subtraction identity back to `EReal`.
  exact_mod_cast hSubReal

/-- Helper for Text 26.4.0.2: at each `x ∈ C`, the closed extension
`F = convexFunctionClosure (fun x => (f x : EReal) + indicatorFunction C x)` satisfies the
Fenchel-Young equality at the coordinate gradient `euclideanGradientAt f x`. -/
lemma helperForText_26_4_0_2_fenchelEquality_for_closedExtension_at_coordinateGradient
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_open : IsOpen C) (hf_diff : DifferentiableOn ℝ f C)
    {fExt : (Fin n → ℝ) → EReal} (hfExt : fExt = fun y => (f y : EReal) + indicatorFunction C y)
    {F : (Fin n → ℝ) → EReal} (hF : F = convexFunctionClosure fExt)
    (hproperExtOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fExt)
    (hproperFOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F)
    {x : Fin n → ℝ} (hx : x ∈ C) :
    fenchelConjugate n F (euclideanGradientAt f x) =
      (((dotProduct x (euclideanGradientAt f x) : ℝ) : EReal) - F x) := by
  have hsubF := helperForText_26_4_0_2_closedExtension_subgradient_at_coordinateGradient
    (hC_open := hC_open) (hf_diff := hf_diff) (hfExt := hfExt) (hF := hF) hproperExtOn hx
  have hFY : FenchelYoungEqualityAt F x (euclideanGradientAt f x) := by
    exact (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      F hproperFOn x (euclideanGradientAt f x)).1.out 0 3).1 hsubF)
  -- Reuse the standalone subtraction-form rewrite so the theorem body only sees one formula.
  exact
    helperForText_26_4_0_2_fenchelYoung_subtractionForm
      (F := F) (x := x) (xStar := euclideanGradientAt f x) hproperFOn hFY

/-- Helper for Text 26.4.0.2: rewriting `L.value_eq` in textbook coordinates expresses the
Legendre value at a source point as the same subtraction formula that appears in Fenchel-Young. -/
lemma helperForText_26_4_0_2_legendreValueEq_coordinate_form
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z)))
    {xE : EuclideanSpace ℝ (Fin n)}
    (hxE : xE ∈ (EuclideanSpace.equiv (Fin n) ℝ).symm '' C) :
    (L.conjFun
      ⟨gradient (fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z)) xE,
        mem_legendreGradientImage
          (C := ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C))
          (f := fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z))
          (x := xE) hxE⟩ : EReal) =
      (((dotProduct ((EuclideanSpace.equiv (Fin n) ℝ) xE)
            (euclideanGradientAt f ((EuclideanSpace.equiv (Fin n) ℝ) xE)) : ℝ) : EReal) -
        (f ((EuclideanSpace.equiv (Fin n) ℝ) xE) : EReal)) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let x : Fin n → ℝ := e xE
  have hx : x ∈ C := by
    rcases hxE with ⟨y, hy, hyEq⟩
    have hyx : y = x := by
      dsimp [x]
      simpa [e] using congrArg e hyEq
    simpa [hyx] using hy
  have hdiffAt : DifferentiableAt ℝ f x :=
    by
      have hsource :
          DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin n) => f (e z)) xE :=
        (L.differentiableOn_source xE hxE).differentiableAt (L.isOpen_source.mem_nhds hxE)
      -- Compose the differentiability of the source-side map with the inverse equivalence.
      simpa [e, x] using hsource.comp (e xE) e.symm.differentiableAt
  have htransport :=
    helperForText_26_4_0_2_sourceGradient_transport (f := f) (x := x) hdiffAt
  have hvalue :
      (L.conjFun
        ⟨gradient (fun z : EuclideanSpace ℝ (Fin n) => f (e z)) xE,
          mem_legendreGradientImage
            (C := e.symm '' C)
            (f := fun z : EuclideanSpace ℝ (Fin n) => f (e z))
            (x := xE) hxE⟩ : EReal) =
        ((((dotProduct (fun i => xE i)
              (fun i => gradient (fun z : EuclideanSpace ℝ (Fin n) => f (e z)) xE i) : ℝ) -
            f (e xE)) : ℝ) : EReal) :=
    congrArg (fun r : ℝ => (r : EReal)) (L.value_eq hxE)
  have hxcoord : (fun i => xE i) = x := by
    rfl
  have hgradcoord :
      (fun i => gradient (fun z : EuclideanSpace ℝ (Fin n) => f (e z)) xE i) =
        euclideanGradientAt f x := by
    simpa [e, x] using htransport
  have hvalue' := hvalue
  rw [hxcoord, hgradcoord] at hvalue'
  -- The Legendre package value formula becomes the coordinate-space subtraction formula after
  -- transporting the gradient through the Euclidean equivalence.
  simpa [e, x, EReal.coe_sub] using hvalue'

-- Proof sketch: extend the convex function `f` from the convex set `C` to a closed proper convex
-- `EReal`-valued function on `ℝ^n` whose effective-domain interior is exactly `C`, then compare
-- the Legendre-conjugate value formula attached to the given transformation datum `L` with the
-- Fenchel-conjugate formula on the gradient image `D`.
/-- Text 26.4.0.2: in the Legendre setting of Definition 26.4.0.1, if `C` is convex and `f` is
convex on `C`, and if we exclude the formal degenerate specialization `n = 0`, `C = ∅`, then `f`
admits a closed proper convex `EReal`-valued extension `F` on `ℝ^n` whose effective-domain
interior is exactly `C`, and the Legendre conjugate `g` agrees on `D` with the ordinary Fenchel
conjugate `F*` of that extension. -/
theorem legendreTransformation_has_closedProperConvexExtension_with_fenchelConjugate_restriction
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hC_convex : Convex ℝ C) (hf_convex : ConvexOn ℝ C f)
    (L : LegendreTransformationOn
      ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
      (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)))
    (hRepair : n ≠ 0 ∨ C.Nonempty) :
    ∃ F : (Fin n → ℝ) → EReal,
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
      LowerSemicontinuous F ∧
      (∀ x ∈ C, F x = (f x : EReal)) ∧
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C ∧
      ∀ xStar : legendreGradientImage
          ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C)
          (fun x : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) x)),
        (L.conjFun xStar : EReal) =
          fenchelConjugate n F (xStar.1 : Fin n → ℝ) := by
  -- Route correction: the header now contains the minimal textbook-compatible repair
  -- `n ≠ 0 ∨ C.Nonempty`, excluding exactly the formal bad specialization `n = 0`, `C = ∅`.
  -- Under this repaired header, the remaining work is no longer a theorem-level contradiction;
  -- it is the substantive construction promised by the text.
  rcases
      helperForText_26_4_0_2_openAndDifferentiableOn_of_legendreDatum (C := C) (f := f) L with
    ⟨hC_open, hf_diff⟩
  by_cases hCne : C.Nonempty
  · -- TODO: construct the closed extension in the nonempty branch by taking the convex closure
    -- of the `+∞` extension from Corollary 25.5.1, then compare `L.conjFun` with the Fenchel
    -- conjugate using the gradient/subgradient bridge furnished by Theorems 25.1 and 23.5.
    let fExt : (Fin n → ℝ) → EReal := fun x => (f x : EReal) + indicatorFunction C x
    let F : (Fin n → ℝ) → EReal := convexFunctionClosure fExt
    have hfExt : fExt = fun y => (f y : EReal) + indicatorFunction C y := rfl
    have hF : F = convexFunctionClosure fExt := rfl
    have hproperExtOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fExt ∧
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fExt) = C := by
      -- Corollary 25.5.1 provides the standard `+∞` extension on the open convex source set.
      simpa [fExt] using
        helperForCorollary_25_5_1_properConvexExtension
          (hCopen := hC_open) (_hCconv := hC_convex) hCne hf_convex
    have hclosedF :
        ClosedConvexFunction F := by
      -- Taking convex closure makes the extension closed without changing it on `C`.
      simpa [F] using
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := fExt) hproperExtOn.1).1.1
    have hproperFOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F := by
      simpa [F] using
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := fExt) hproperExtOn.1).1.2
    have hproperF :
        ProperConvexERealFunction (F := (Fin n → ℝ)) F := by
      exact
        helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn hproperFOn
    have hagreeF : ∀ x ∈ C, F x = (f x : EReal) := by
      intro x hx
      have hxInt : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fExt) := by
        simpa [hproperExtOn.2] using hx
      have hclEq : convexFunctionClosure fExt x = fExt x :=
        helperForCorollary_25_1_1_1_closure_eq_at_interior_point hproperExtOn.1 hxInt
      -- On the original open set, the closure agrees with the extension, and the extension is
      -- just the original real-valued function.
      simpa [F, fExt, add_indicatorFunction_eq, hx] using hclEq
    have hInteriorF :
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = C := by
      have hC_subset_dom : C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) F := by
        intro x hx
        rw [effectiveDomain_eq]
        refine ⟨by simp, ?_⟩
        have hEq : F x = (f x : EReal) := hagreeF x hx
        exact lt_top_iff_ne_top.mpr (by simpa [hEq])
      have hC_subset_int :
          C ⊆ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) := by
        intro x hx
        refine mem_interior_iff_mem_nhds.2 ?_
        exact Filter.mem_of_superset (hC_open.mem_nhds hx) hC_subset_dom
      have hInt_subset_C :
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) ⊆ C := by
        intro x hx
        have hxExt :
            x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fExt) :=
          helperForCorollary_25_1_2_mem_interior_effectiveDomain_of_closure_mem_interior
            hproperExtOn.1 hx
        simpa [hproperExtOn.2] using hxExt
      exact Set.Subset.antisymm hInt_subset_C hC_subset_int
    refine ⟨F, hproperF, hclosedF.2, hagreeF, hInteriorF, ?_⟩
    intro xStar
    rcases xStar with ⟨xStar, hxStar⟩
    rcases hxStar with ⟨xE, hxE, rfl⟩
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let x : Fin n → ℝ := e xE
    have hx : x ∈ C := by
      rcases hxE with ⟨y, hy, hyEq⟩
      have hyx : y = x := by
        dsimp [x]
        simpa [e] using congrArg e hyEq
      simpa [hyx] using hy
    have hvalue :
        (L.conjFun
          ⟨gradient (fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z))
              xE,
            mem_legendreGradientImage
              (C := ((EuclideanSpace.equiv (Fin n) ℝ).symm '' C))
              (f := fun z : EuclideanSpace ℝ (Fin n) => f ((EuclideanSpace.equiv (Fin n) ℝ) z))
              (x := xE) hxE⟩ : EReal) =
          (((dotProduct x (euclideanGradientAt f x) : ℝ) : EReal) - (f x : EReal)) :=
      helperForText_26_4_0_2_legendreValueEq_coordinate_form (C := C) (f := f) L hxE
    have hfenchel :=
      helperForText_26_4_0_2_fenchelEquality_for_closedExtension_at_coordinateGradient
        (C := C) (f := f) (hC_open := hC_open) (hf_diff := hf_diff)
        (hfExt := hfExt) (hF := hF) hproperExtOn.1 hproperFOn hx
    have hfenchel' :
        fenchelConjugate n F (euclideanGradientAt f x) =
          (((dotProduct x (euclideanGradientAt f x) : ℝ) : EReal) - (f x : EReal)) := by
      -- Replace the closed extension value `F x` by the original value `f x` on the source set.
      simpa [hagreeF x hx] using hfenchel
    have htransport :=
      helperForText_26_4_0_2_sourceGradient_transport (f := f) (x := x)
        ((hf_diff x hx).differentiableAt (hC_open.mem_nhds hx))
    have htransport' :
        (((gradient
            (fun z : EuclideanSpace ℝ (Fin n) =>
              f ((EuclideanSpace.equiv (Fin n) ℝ) z))
            xE : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ)) =
          euclideanGradientAt f x := by
      simpa [e, x] using htransport
    -- Both sides reduce to the same subtraction formula at the transported coordinate gradient.
    exact hvalue.trans (by simpa [htransport'] using hfenchel'.symm)
  · have hn : n ≠ 0 := by
      rcases hRepair with hn | hCne' 
      · exact hn
      · exact (hCne hCne').elim
    have hC_empty : C = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.mpr (fun x hx => hCne ⟨x, hx⟩)
    rcases
        helperForText_26_4_0_2_indicatorSingletonPackage_of_emptySource (n := n) hn with
      ⟨hproper, hls, hInterior⟩
    refine
      ⟨indicatorFunction ({0} : Set (Fin n → ℝ)), hproper, hls, ?_, ?_, ?_⟩
    · -- The extension-agreement clause is vacuous because `C` is empty in this branch.
      intro x hx
      exact (hCne ⟨x, hx⟩).elim
    · -- The packaged singleton witness was chosen precisely so that its interior domain is empty.
      simpa [hC_empty] using hInterior
    · intro xStar
      -- The Legendre target is empty when the source set is empty, so there is no restriction
      -- value left to check.
      have hxStar_false : False := by
        exact
          helperForText_26_4_0_2_false_of_mem_emptyGradientImage
            (f := fun x : EuclideanSpace ℝ (Fin n) =>
              f ((EuclideanSpace.equiv (Fin n) ℝ) x))
            (xStar := xStar.1)
            (by simpa [hC_empty] using xStar.2)
      exact hxStar_false.elim

-- Proof sketch: use Theorem 25.1 on each point of `int (dom f)` to identify the gradient with
-- the unique Euclidean subgradient, then apply Theorem 23.5 to convert the resulting
-- Fenchel-Young equalities into a well-defined Legendre package whose target is exactly the
-- gradient image and whose values agree with `f*` on that target.

end Section26
end Chap05

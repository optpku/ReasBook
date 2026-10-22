/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

private noncomputable abbrev compactRightInfimum {X : Type u} {Y : Type v}
    (φ : X × Y → EReal) : X → EReal :=
  fun x ↦ sInf (Set.range fun y : Y ↦ φ (x, y))

private theorem compactRightInfimum_eq_of_isMinOn {X : Type u} {Y : Type v}
    {φ : X × Y → EReal} {x : X} {y : Y}
    (hy : IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y) :
    compactRightInfimum φ x = φ (x, y) := by
  rw [isMinOn_iff] at hy
  have hglb : IsGLB (Set.range fun y' : Y ↦ φ (x, y')) (φ (x, y)) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases hz with ⟨z, rfl⟩
      exact hy z (by simp)
    · intro b hb
      exact hb ⟨y, rfl⟩
  simpa [compactRightInfimum] using (hglb.unique (isGLB_sInf _)).symm

private lemma fiber_exists_isMinOn {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] {φ : X × Y → EReal} (hφ : LowerSemicontinuous φ) :
    ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y := by
  intro x
  have hfiber : LowerSemicontinuous (fun y : Y ↦ φ (x, y)) := by
    simpa using hφ.comp (by
      continuity : Continuous fun y : Y ↦ (x, y))
  obtain ⟨y, -, hy⟩ :=
    (hfiber.lowerSemicontinuousOn Set.univ).exists_isMinOn Set.univ_nonempty isCompact_univ
  exact ⟨y, hy⟩

private lemma compactRightInfimum_epigraph_eq_image_fst {X : Type u} {Y : Type v}
    {φ : X × Y → EReal}
    (hmin : ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y) :
    {p : X × EReal | compactRightInfimum φ p.1 ≤ p.2} =
      Prod.fst '' {q : (X × EReal) × Y | φ (q.1.1, q.2) ≤ q.1.2} := by
  ext p
  constructor
  · intro hp
    obtain ⟨y, hy⟩ := hmin p.1
    refine ⟨(p, y), ?_, rfl⟩
    simpa [compactRightInfimum_eq_of_isMinOn hy] using hp
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨⟨x, t⟩, y⟩
    have hy : φ (x, y) ∈ Set.range fun y' : Y ↦ φ (x, y') := ⟨y, rfl⟩
    exact le_trans (sInf_le hy) hq

private lemma isClosed_epigraph_compactRightInfimum {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] {φ : X × Y → EReal} (hφ : LowerSemicontinuous φ) :
    IsClosed {p : X × EReal | compactRightInfimum φ p.1 ≤ p.2} := by
  let e : ((X × EReal) × Y) → (X × Y) × EReal := fun q ↦ ((q.1.1, q.2), q.1.2)
  have he : Continuous e := by
    fun_prop
  have hclosedFiberEpigraph : IsClosed {q : (X × EReal) × Y | φ (q.1.1, q.2) ≤ q.1.2} := by
    simpa [e] using
      (LowerSemicontinuous.isClosed_epigraph hφ).preimage he
  have hmin : ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y :=
    fiber_exists_isMinOn hφ
  rw [compactRightInfimum_epigraph_eq_image_fst hmin]
  exact isClosedMap_fst_of_compactSpace _ hclosedFiberEpigraph

/-- Lemma 1.30: over a nonempty compact second factor, the infimum of a lower semicontinuous
extended-real-valued function over the second variable is lower semicontinuous, and each fiber
section attains its minimum. -/
theorem lowerSemicontinuous_compactRightInfimum_and_exists_isMinOn
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] {φ : X × Y → EReal}
    (hφ : LowerSemicontinuous φ) :
    LowerSemicontinuous (fun x ↦ sInf (Set.range fun y : Y ↦ φ (x, y))) ∧
      ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y := by
  have hmin : ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y :=
    fiber_exists_isMinOn hφ
  refine ⟨?_, hmin⟩
  change LowerSemicontinuous (compactRightInfimum φ)
  rw [lowerSemicontinuous_iff_isClosed_epigraph]
  exact isClosed_epigraph_compactRightInfimum hφ

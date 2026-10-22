/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Semicontinuity.Defs

open scoped Topology

-- Semantic recall checked: mathlib's canonical owner notions here are `ContinuousWithinAt`,
-- `UpperSemicontinuousWithinAt`, and `LowerSemicontinuousWithinAt`. The source's directional
-- variants are the corresponding one-dimensional within-set properties along every line
-- `t ↦ x + t • d` inside `D`.

section AlongLine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `AlongLineWithinAt P D F x` means that `F` satisfies the within-at owner `P` along every
line through `x` that stays inside `D`. -/
def AlongLineWithinAt
    {G : Type*}
    (P : (ℝ → G) → Set ℝ → ℝ → Prop)
    (D : Set E)
    (F : E → G)
    (x : E) : Prop :=
  x ∈ D ∧
    ∀ d : E, P (fun t ↦ F (x + t • d)) {t : ℝ | x + t • d ∈ D} 0

/-- `AlongLineWithinAt` is proposition-valued. -/
noncomputable instance instDecidableAlongLineWithinAt
    {G : Type*}
    (P : (ℝ → G) → Set ℝ → ℝ → Prop)
    (D : Set E)
    (F : E → G)
    (x : E) :
    Decidable (AlongLineWithinAt P D F x) :=
  Classical.propDecidable _

/-- Unfolding lemma for `AlongLineWithinAt`. -/
theorem alongLineWithinAt_iff
    {G : Type*}
    (P : (ℝ → G) → Set ℝ → ℝ → Prop)
    (D : Set E)
    (F : E → G)
    (x : E) :
    AlongLineWithinAt P D F x ↔
      x ∈ D ∧
        ∀ d : E, P (fun t ↦ F (x + t • d)) {t : ℝ | x + t • d ∈ D} 0 :=
  Iff.rfl

/-- `AlongLineWithinAt` records that `x ∈ D`. -/
theorem AlongLineWithinAt.mem
    {G : Type*}
    {P : (ℝ → G) → Set ℝ → ℝ → Prop}
    {D : Set E}
    {F : E → G}
    {x : E}
    (h : AlongLineWithinAt P D F x) :
    x ∈ D :=
  h.1

end AlongLine

section Directional

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Value" => EuclideanSpace ℝ (Fin m)

/-- `AlongLineCoordWithinAt P D F x` means that every coordinate of `F` satisfies the scalar
within-at owner `P` along every line through `x` that stays inside `D`. -/
def AlongLineCoordWithinAt
    (P : (ℝ → ℝ) → Set ℝ → ℝ → Prop)
    (D : Set Point)
    (F : Point → Value)
    (x : Point) : Prop :=
  x ∈ D ∧
    ∀ d : Point, ∀ i : Fin m,
      P (fun t ↦ F (x + t • d) i) {t : ℝ | x + t • d ∈ D} 0

/-- `AlongLineCoordWithinAt` is proposition-valued. -/
noncomputable instance instDecidableAlongLineCoordWithinAt
    (P : (ℝ → ℝ) → Set ℝ → ℝ → Prop)
    (D : Set Point)
    (F : Point → Value)
    (x : Point) :
    Decidable (AlongLineCoordWithinAt P D F x) :=
  Classical.propDecidable _

/-- Unfolding lemma for `AlongLineCoordWithinAt`. -/
theorem alongLineCoordWithinAt_iff
    (P : (ℝ → ℝ) → Set ℝ → ℝ → Prop)
    (D : Set Point)
    (F : Point → Value)
    (x : Point) :
    AlongLineCoordWithinAt P D F x ↔
      x ∈ D ∧
        ∀ d : Point, ∀ i : Fin m,
          P (fun t ↦ F (x + t • d) i) {t : ℝ | x + t • d ∈ D} 0 :=
  Iff.rfl

/-- Source-facing owner for Chapter01 Definition 1.2.21 (1): `F : D ⊆ ℝⁿ → ℝᵐ` is
directionally hemi-continuous at `x ∈ D` when every line through `x` inside `D`
is continuous at `0`. -/
abbrev DirectionalHemicontinuousWithinAt
    (D : Set Point)
    (F : Point → Value)
    (x : Point) : Prop :=
  AlongLineWithinAt ContinuousWithinAt D F x

/-- Helper for Chapter01 Definition 1.2.21: a neighborhood-within statement along the line
`t ↦ x + t • d` is equivalent to an explicit small-`|t|` condition inside `D`. -/
lemma withinLineNeighborhood_iff_existsDelta
    (D : Set Point)
    (x d : Point)
    (P : ℝ → Prop) :
    {t : ℝ | P t} ∈ 𝓝[{t : ℝ | x + t • d ∈ D}] 0 ↔
      ∃ δ > 0, ∀ t : ℝ, |t| < δ → x + t • d ∈ D → P t := by
  constructor
  · intro hP
    -- Unpack the within-neighborhood into a metric ball around `0`.
    rcases Metric.mem_nhdsWithin_iff.mp hP with ⟨δ, hδ, hδP⟩
    refine ⟨δ, hδ, ?_⟩
    intro t ht hmem
    exact hδP ⟨by simpa [Metric.mem_ball, Real.dist_0_eq_abs] using ht, hmem⟩
  · rintro ⟨δ, hδ, hP⟩
    -- Repackage the explicit `δ` control back into a within-neighborhood.
    refine Metric.mem_nhdsWithin_iff.mpr ⟨δ, hδ, ?_⟩
    intro t ht
    exact hP t (by simpa [Metric.mem_ball, Real.dist_0_eq_abs] using ht.1) ht.2

/-- Helper for Chapter01 Definition 1.2.21: finitely many upper semicontinuous coordinates
admit one eventual bound `∀ i, g i z < g i a + ε`. -/
lemma upperSemicontinuousWithinAt_forall_eventually_lt_add
    {α : Type*} [TopologicalSpace α]
    {s : Set α}
    {a : α}
    (g : Fin m → α → ℝ)
    (hg : ∀ i : Fin m, UpperSemicontinuousWithinAt (g i) s a) :
    ∀ ε > 0, ∀ᶠ z in 𝓝[s] a, ∀ i : Fin m, g i z < g i a + ε := by
  intro ε hε
  -- Combine the coordinatewise eventual estimates into one finite conjunction.
  rw [Filter.eventually_all]
  intro i
  exact (upperSemicontinuousWithinAt_iff.mp (hg i)) _ (lt_add_of_pos_right _ hε)

/-- Helper for Chapter01 Definition 1.2.21: finitely many lower semicontinuous coordinates
admit one eventual bound `∀ i, g i a - ε < g i z`. -/
lemma lowerSemicontinuousWithinAt_forall_eventually_sub_lt
    {α : Type*} [TopologicalSpace α]
    {s : Set α}
    {a : α}
    (g : Fin m → α → ℝ)
    (hg : ∀ i : Fin m, LowerSemicontinuousWithinAt (g i) s a) :
    ∀ ε > 0, ∀ᶠ z in 𝓝[s] a, ∀ i : Fin m, g i a - ε < g i z := by
  intro ε hε
  -- Combine the coordinatewise eventual estimates into one finite conjunction.
  rw [Filter.eventually_all]
  intro i
  exact (lowerSemicontinuousWithinAt_iff.mp (hg i)) _ (sub_lt_self _ hε)

/-- Chapter01 Definition 1.2.21 (1): `DirectionalHemicontinuousWithinAt D F x`
is equivalent to the source directional `ε`-`δ` condition
`‖F (x + t • d) - F x‖ < ε` for sufficiently small `t` with `x + t • d ∈ D`. -/
theorem directionalHemicontinuousWithinAt_iff
    (D : Set Point)
    (F : Point → Value)
    (x : Point) :
    DirectionalHemicontinuousWithinAt D F x ↔
      x ∈ D ∧
        ∀ d : Point, ∀ ε > 0,
          ∃ δ > 0, ∀ t : ℝ,
            |t| < δ → x + t • d ∈ D → ‖F (x + t • d) - F x‖ < ε := by
  simp only [DirectionalHemicontinuousWithinAt, alongLineWithinAt_iff]
  constructor
  · rintro ⟨hx, hcont⟩
    refine ⟨hx, ?_⟩
    intro d ε hε
    -- Convert continuity along the line to an eventual metric estimate near `t = 0`.
    have hEventualNorm :
        ∀ᶠ t in 𝓝[{t : ℝ | x + t • d ∈ D}] 0, ‖F (x + t • d) - F x‖ < ε := by
      simpa [zero_smul, add_zero, dist_eq_norm] using
        (Metric.continuousWithinAt_iff'.mp (hcont d)) ε hε
    -- Extract a concrete `δ` from the within-neighborhood statement.
    exact (withinLineNeighborhood_iff_existsDelta D x d
      (fun t ↦ ‖F (x + t • d) - F x‖ < ε)).mp hEventualNorm
  · rintro ⟨hx, hδ⟩
    refine ⟨hx, ?_⟩
    intro d
    -- Rebuild `ContinuousWithinAt` from the directional `ε`-`δ` control.
    rw [Metric.continuousWithinAt_iff']
    intro ε hε
    rcases hδ d ε hε with ⟨δ, hδpos, hbound⟩
    have hEventualNorm :
        ∀ᶠ t in 𝓝[{t : ℝ | x + t • d ∈ D}] 0, ‖F (x + t • d) - F x‖ < ε :=
      (withinLineNeighborhood_iff_existsDelta D x d
        (fun t ↦ ‖F (x + t • d) - F x‖ < ε)).mpr ⟨δ, hδpos, hbound⟩
    simpa [zero_smul, add_zero, dist_eq_norm] using hEventualNorm

/-- Chapter01 Definition 1.2.21 (2): `F : D ⊆ ℝⁿ → ℝᵐ` is upper hemi-continuous at `x ∈ D`
if every direction `d` admits a directional `ε`-`δ` control where each coordinate satisfies
`F (x + t • d) i < F x i + ε` for sufficiently small `t`. -/
abbrev UpperDirectionalHemicontinuousWithinAt
    (D : Set Point)
    (F : Point → Value)
    (x : Point) : Prop :=
  AlongLineCoordWithinAt UpperSemicontinuousWithinAt D F x

/-- Unfolding lemma for `UpperDirectionalHemicontinuousWithinAt`. -/
theorem upperDirectionalHemicontinuousWithinAt_iff
    (D : Set Point)
    (F : Point → Value)
    (x : Point) :
    UpperDirectionalHemicontinuousWithinAt D F x ↔
      x ∈ D ∧
        ∀ d : Point, ∀ ε > 0,
          ∃ δ > 0, ∀ t : ℝ,
            |t| < δ → x + t • d ∈ D →
              ∀ i : Fin m, F (x + t • d) i < F x i + ε := by
  simp only [UpperDirectionalHemicontinuousWithinAt, alongLineCoordWithinAt_iff]
  constructor
  · rintro ⟨hx, hupper⟩
    refine ⟨hx, ?_⟩
    intro d ε hε
    -- Package the coordinatewise upper semicontinuity into one eventual `∀ i` bound.
    have hEventual :
        ∀ᶠ t in 𝓝[{t : ℝ | x + t • d ∈ D}] 0,
          ∀ i : Fin m, F (x + t • d) i < F x i + ε := by
      simpa [zero_smul, add_zero] using
        upperSemicontinuousWithinAt_forall_eventually_lt_add
          (g := fun i t ↦ F (x + t • d) i)
          (a := 0)
          (s := {t : ℝ | x + t • d ∈ D})
          (fun i ↦ hupper d i) ε hε
    -- Translate the eventual bound into a single directional `δ`.
    rcases (withinLineNeighborhood_iff_existsDelta D x d
      (fun t ↦ ∀ i : Fin m, F (x + t • d) i < F x i + ε)).mp hEventual with
      ⟨δ, hδpos, hbound⟩
    exact ⟨δ, hδpos, hbound⟩
  · rintro ⟨hx, hδ⟩
    refine ⟨hx, ?_⟩
    intro d i
    -- Recover coordinatewise upper semicontinuity from the shared directional `δ`.
    rw [upperSemicontinuousWithinAt_iff]
    intro y hy
    have hε : 0 < y - F x i := by
      apply sub_pos.mpr
      simpa [zero_smul, add_zero] using hy
    rcases hδ d (y - F x i) hε with ⟨δ, hδpos, hbound⟩
    refine (withinLineNeighborhood_iff_existsDelta D x d
      (fun t ↦ F (x + t • d) i < y)).mpr ?_
    refine ⟨δ, hδpos, ?_⟩
    intro t ht hmem
    have hcoord := hbound t ht hmem i
    linarith

/-- Chapter01 Definition 1.2.21 (3): `F : D ⊆ ℝⁿ → ℝᵐ` is lower hemi-continuous at `x ∈ D`
if every direction `d` admits a directional `ε`-`δ` control where each coordinate satisfies
`F x i - ε < F (x + t • d) i` for sufficiently small `t`. -/
abbrev LowerDirectionalHemicontinuousWithinAt
    (D : Set Point)
    (F : Point → Value)
    (x : Point) : Prop :=
  AlongLineCoordWithinAt LowerSemicontinuousWithinAt D F x

/-- Unfolding lemma for `LowerDirectionalHemicontinuousWithinAt`. -/
theorem lowerDirectionalHemicontinuousWithinAt_iff
    (D : Set Point)
    (F : Point → Value)
    (x : Point) :
    LowerDirectionalHemicontinuousWithinAt D F x ↔
      x ∈ D ∧
        ∀ d : Point, ∀ ε > 0,
          ∃ δ > 0, ∀ t : ℝ,
            |t| < δ → x + t • d ∈ D →
              ∀ i : Fin m, F x i - ε < F (x + t • d) i := by
  simp only [LowerDirectionalHemicontinuousWithinAt, alongLineCoordWithinAt_iff]
  constructor
  · rintro ⟨hx, hlower⟩
    refine ⟨hx, ?_⟩
    intro d ε hε
    -- Package the coordinatewise lower semicontinuity into one eventual `∀ i` bound.
    have hEventual :
        ∀ᶠ t in 𝓝[{t : ℝ | x + t • d ∈ D}] 0,
          ∀ i : Fin m, F x i - ε < F (x + t • d) i := by
      simpa [zero_smul, add_zero] using
        lowerSemicontinuousWithinAt_forall_eventually_sub_lt
          (g := fun i t ↦ F (x + t • d) i)
          (a := 0)
          (s := {t : ℝ | x + t • d ∈ D})
          (fun i ↦ hlower d i) ε hε
    -- Translate the eventual bound into a single directional `δ`.
    rcases (withinLineNeighborhood_iff_existsDelta D x d
      (fun t ↦ ∀ i : Fin m, F x i - ε < F (x + t • d) i)).mp hEventual with
      ⟨δ, hδpos, hbound⟩
    exact ⟨δ, hδpos, hbound⟩
  · rintro ⟨hx, hδ⟩
    refine ⟨hx, ?_⟩
    intro d i
    -- Recover coordinatewise lower semicontinuity from the shared directional `δ`.
    rw [lowerSemicontinuousWithinAt_iff]
    intro y hy
    have hε : 0 < F x i - y := by
      apply sub_pos.mpr
      simpa [zero_smul, add_zero] using hy
    rcases hδ d (F x i - y) hε with ⟨δ, hδpos, hbound⟩
    refine (withinLineNeighborhood_iff_existsDelta D x d
      (fun t ↦ y < F (x + t • d) i)).mpr ?_
    refine ⟨δ, hδpos, ?_⟩
    intro t ht hmem
    have hcoord := hbound t ht hmem i
    linarith

end Directional

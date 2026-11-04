/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron

open scoped Pointwise
open scoped Matrix

section RecessionCone

variable {R E : Type*}

/-- Definition 3.6-extra-1 (1). The recession cone of `P` consists of the directions `r` such
that every point of `P` remains in `P` after translation by any nonnegative `R`-multiple of `r`.
-/
def recessionCone (R : Type*) [Zero R] [LE R] {E : Type*} [Add E] [SMul R E]
    (P : Set E) : Set E :=
  {r : E | ∀ ⦃x : E⦄, x ∈ P → ∀ a : R, 0 ≤ a → x + a • r ∈ P}

/-- Membership in `recessionCone R P` unfolds to the defining nonnegative-ray condition. -/
theorem mem_recessionCone_iff
    [Zero R] [LE R] [Add E] [SMul R E]
    {P : Set E} {r : E} :
    r ∈ recessionCone R P ↔
      ∀ ⦃x : E⦄, x ∈ P → ∀ a : R, 0 ≤ a → x + a • r ∈ P := by
  rfl

/-- The zero vector is always a recession direction. -/
lemma zero_mem_recessionCone
    [Zero R] [LE R] [AddMonoid E] [SMulZeroClass R E]
    {P : Set E} :
    (0 : E) ∈ recessionCone R P := by
  rw [mem_recessionCone_iff]
  intro x hx a ha
  rw [smul_zero, add_zero]
  exact hx

section Pointed

variable [Semiring R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommMonoid E] [Module R E]

/-- Recession directions are closed under nonnegative scalar multiplication. -/
lemma smul_mem_recessionCone
    {P : Set E} {r : E}
    (hr : r ∈ recessionCone R P) {a : R} (ha : 0 ≤ a) :
    a • r ∈ recessionCone R P := by
  rw [mem_recessionCone_iff] at hr ⊢
  intro x hx b hb
  have hba : 0 ≤ b * a := mul_nonneg hb ha
  have hxr : x + (b * a) • r ∈ P := hr hx (b * a) hba
  simpa [smul_smul] using hxr

/-- Bridge/view: the recession directions of `P` form a pointed cone. -/
def recessionPointedCone
    (R : Type*) [Semiring R] [PartialOrder R] [IsOrderedRing R]
    {E : Type*} [AddCommMonoid E] [Module R E] (P : Set E) : PointedCone R E where
  carrier := recessionCone R P
  zero_mem' := zero_mem_recessionCone
  add_mem' {r s} hr hs := by
    rw [mem_recessionCone_iff] at hr hs ⊢
    intro x hx a ha
    simpa [smul_add, add_assoc, add_left_comm, add_comm] using hs (hr hx a ha) a ha
  smul_mem' a r hr := by
    simpa using smul_mem_recessionCone hr a.2

end Pointed

end RecessionCone

section LinealitySpace

variable {R E : Type*}

/-- Definition 3.6-extra-1 (2). The lineality space of `P` consists of the directions `r` such
that every point of `P` remains in `P` after translation by any `R`-multiple of `r`. -/
def linealitySpace (R : Type*) {E : Type*} [Add E] [SMul R E] (P : Set E) : Set E :=
  {r : E | ∀ ⦃x : E⦄, x ∈ P → ∀ a : R, x + a • r ∈ P}

/-- Membership in `linealitySpace R P` unfolds to the defining all-scalars translation condition.
-/
theorem mem_linealitySpace_iff
    [Add E] [SMul R E]
    {P : Set E} {r : E} :
    r ∈ linealitySpace R P ↔
      ∀ ⦃x : E⦄, x ∈ P → ∀ a : R, x + a • r ∈ P := by
  rfl

/-- Helper for Definition 3.6-extra-1: the zero vector always belongs to the lineality space. -/
lemma zero_mem_linealitySpace
    [Zero R] [AddMonoid E] [SMulZeroClass R E]
    {P : Set E} :
    (0 : E) ∈ linealitySpace R P := by
  rw [mem_linealitySpace_iff]
  intro x hx a
  have hx0 : x + (0 : E) ∈ P := by
    simpa [add_zero] using hx
  simpa [smul_zero] using hx0

/-- Definition 3.6-extra-1 (4). A set is pointed when its lineality space is exactly `{0}`; for
nonempty polyhedra this recovers the source notion. -/
def is_pointed (R : Type*) {E : Type*} [Add E] [SMul R E] [Zero E] (P : Set E) : Prop :=
  linealitySpace R P = ({0} : Set E)

/-- The defining expansion of `is_pointed`. -/
theorem is_pointed_iff
    [Add E] [SMul R E] [Zero E]
    {P : Set E} :
    is_pointed R P ↔ linealitySpace R P = ({0} : Set E) := by
  rfl

/-- `is_pointed` means that no nonzero vector lies in the lineality space. -/
theorem is_pointed_iff_eq_zero_of_mem_linealitySpace
    [Zero R] [AddMonoid E] [SMulZeroClass R E]
    {P : Set E} :
    is_pointed R P ↔ ∀ r : E, r ∈ linealitySpace R P → r = 0 := by
  constructor
  · intro hP r hr
    rw [is_pointed_iff] at hP
    have hr_zero : r ∈ ({0} : Set E) := by
      rw [← hP]
      exact hr
    simpa using hr_zero
  · intro hzero
    rw [is_pointed_iff]
    ext r
    constructor
    · intro hr
      rw [Set.mem_singleton_iff]
      exact hzero r hr
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      rw [hr]
      exact zero_mem_linealitySpace

end LinealitySpace

section RecessionNeg

variable {R E : Type*} [Zero R] [LE R]
variable [AddCommGroup E] [SMul R E]

/-- Helper for Definition 3.6-extra-1: membership in the pointwise negation of the recession cone
means that the opposite vector is a recession direction. -/
lemma mem_neg_recessionCone_iff
    {P : Set E} {r : E} :
    r ∈ -recessionCone R P ↔ -r ∈ recessionCone R P := by
  simp

end RecessionNeg

section RecessionLinealityBridge

variable {R E : Type*} [LinearOrder R] [Ring R] [IsOrderedRing R]
variable [AddCommGroup E] [Module R E]

/-- Definition 3.6-extra-1 (3). The lineality space of `P` is the intersection of its recession
cone with the negative of its recession cone. -/
theorem linealitySpace_eq_recessionCone_inter_neg
    (P : Set E) :
    linealitySpace R P = recessionCone R P ∩ -recessionCone R P := by
  ext r
  constructor
  · intro hr
    rw [Set.mem_inter_iff]
    rw [mem_linealitySpace_iff] at hr
    constructor
    · rw [mem_recessionCone_iff]
      intro x hx a ha
      exact hr hx a
    · rw [mem_neg_recessionCone_iff, mem_recessionCone_iff]
      intro x hx a ha
      simpa [smul_neg, neg_smul] using hr hx (-a)
  · intro hr
    rw [Set.mem_inter_iff] at hr
    rw [mem_linealitySpace_iff]
    have hr_pos : r ∈ recessionCone R P := hr.1
    have hr_neg : -r ∈ recessionCone R P := by
      rw [← mem_neg_recessionCone_iff]
      exact hr.2
    rw [mem_recessionCone_iff] at hr_pos hr_neg
    intro x hx a
    by_cases ha : 0 ≤ a
    · exact hr_pos hx a ha
    · have hneg : 0 ≤ -a := le_of_lt (neg_pos.mpr (lt_of_not_ge ha))
      simpa [smul_neg, neg_smul] using hr_neg hx (-a) hneg

end RecessionLinealityBridge

section LinealitySubmodule

variable {R E : Type*} [LinearOrder R] [Ring R] [IsOrderedRing R]
variable [AddCommGroup E] [Module R E]

/-- The lineality directions of `P` form the lineal submodule of its recession cone. -/
noncomputable def linealitySubmodule (R : Type*) [LinearOrder R] [Ring R] [IsOrderedRing R]
    {E : Type*} [AddCommGroup E] [Module R E] (P : Set E) : Submodule R E :=
  (recessionPointedCone R P).lineal

/-- Membership in the lineality submodule is the original lineality predicate. -/
theorem mem_linealitySubmodule_iff
    {P : Set E} {r : E} :
    r ∈ linealitySubmodule R P ↔ r ∈ linealitySpace R P := by
  change r ∈ (recessionPointedCone R P).lineal ↔ r ∈ linealitySpace R P
  rw [PointedCone.mem_lineal, linealitySpace_eq_recessionCone_inter_neg, Set.mem_inter_iff,
    mem_neg_recessionCone_iff]
  change (r ∈ recessionCone R P ∧ -r ∈ recessionCone R P) ↔
    (r ∈ recessionCone R P ∧ -r ∈ recessionCone R P)
  rfl

@[simp] theorem coe_linealitySubmodule
    (P : Set E) :
    (linealitySubmodule R P : Set E) = linealitySpace R P := by
  ext r
  exact mem_linealitySubmodule_iff

end LinealitySubmodule

/- In the real-vector-space chapter, the source-facing owners and their canonical submodule bridge
are used with the default scalar `ℝ`; the raw owners remain available as
`_root_.recessionCone`, `_root_.linealitySpace`, `_root_.is_pointed`, and
`_root_.linealitySubmodule`. -/
notation "recessionCone" => _root_.recessionCone ℝ
notation "linealitySpace" => _root_.linealitySpace ℝ
notation "is_pointed" => _root_.is_pointed ℝ
notation "linealitySubmodule" => _root_.linealitySubmodule ℝ

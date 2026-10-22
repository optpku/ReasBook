/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set

universe u

variable {Ω : Type u}

/-- Definition 1.13 (1): the set-theoretic limes inferior of a sequence of subsets of `Ω` is the
canonical filter `liminf` along `atTop`; for a sequence this is the union of the tail
intersections. -/
theorem set_liminf_eq_iUnion_iInter (A : ℕ → Set Ω) :
    liminf A atTop = ⋃ n : ℕ, ⋂ m ≥ n, A m := by
  simpa using
    (liminf_eq_iSup_iInf_of_nat : liminf A atTop = ⨆ n : ℕ, ⨅ m ≥ n, A m)

/-- Membership in the set-theoretic `liminf` means eventual membership in the sequence of sets. -/
theorem mem_set_liminf_iff {A : ℕ → Set Ω} {x : Ω} :
    x ∈ liminf A atTop ↔ ∃ n : ℕ, ∀ m ≥ n, x ∈ A m := by
  rw [liminf_eq_iSup_iInf_of_nat]
  simp

/-- Definition 1.13 (2): the set-theoretic limes superior of a sequence of subsets of `Ω` is the
canonical filter `limsup` along `atTop`; for a sequence this is the intersection of the tail
unions. -/
theorem set_limsup_eq_iInter_iUnion (A : ℕ → Set Ω) :
    limsup A atTop = ⋂ n : ℕ, ⋃ m ≥ n, A m := by
  simpa using
    (limsup_eq_iInf_iSup_of_nat : limsup A atTop = ⨅ n : ℕ, ⨆ m ≥ n, A m)

/-- Membership in the set-theoretic `limsup` means that every tail contains a set containing the
point. -/
theorem mem_set_limsup_iff {A : ℕ → Set Ω} {x : Ω} :
    x ∈ limsup A atTop ↔ ∀ n : ℕ, ∃ m ≥ n, x ∈ A m := by
  rw [limsup_eq_iInf_iSup_of_nat]
  simp

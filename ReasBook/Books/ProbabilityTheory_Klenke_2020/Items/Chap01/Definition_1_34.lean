/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

variable {α : Type u}

/-- Definition 1.34 (1): A sequence of sets increases to `A` if it is monotone with respect to
inclusion and its union is `A`. -/
class Set.IncreasesTo (s : ℕ → Set α) (A : outParam (Set α)) : Prop where
  /-- The sequence is increasing with respect to inclusion. -/
  mono : Monotone s
  /-- The union of the sequence is the limiting set `A`. -/
  iUnion_eq : (⋃ n, s n) = A

/-- An increasing sequence of sets is canonically monotone. -/
instance instMonotoneOfIncreasesTo {s : ℕ → Set α} {A : Set α} [h : Set.IncreasesTo s A] :
    Monotone s :=
  h.mono

/-- Definition 1.34 (2): A sequence of sets decreases to `A` if it is antitone with respect to
inclusion and its intersection is `A`. -/
class Set.DecreasesTo (s : ℕ → Set α) (A : outParam (Set α)) : Prop where
  /-- The sequence is decreasing with respect to inclusion. -/
  antitone : Antitone s
  /-- The intersection of the sequence is the limiting set `A`. -/
  iInter_eq : (⋂ n, s n) = A

/-- A decreasing sequence of sets is canonically antitone. -/
instance instAntitoneOfDecreasesTo {s : ℕ → Set α} {A : Set α} [h : Set.DecreasesTo s A] :
    Antitone s :=
  h.antitone

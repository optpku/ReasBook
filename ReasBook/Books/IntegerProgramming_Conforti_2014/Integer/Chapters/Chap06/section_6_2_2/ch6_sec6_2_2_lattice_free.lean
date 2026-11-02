import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Basic

open Set
open scoped IntegerVectorNotation

section LatticeFree

variable {E : Type*}

/-- A set `K ⊆ E` is `S`-free when its interior contains no point of the forbidden set `S`. -/
def is_free_of [TopologicalSpace E] (S : Set E) (K : Set E) : Prop :=
  Disjoint (interior K) S

/-- A set is `S`-free exactly when no point of the forbidden set `S` lies in its interior. -/
theorem is_free_of_iff
    [TopologicalSpace E]
    {S K : Set E} :
    is_free_of S K ↔ ∀ x ∈ S, x ∉ interior K := by
  rw [is_free_of, disjoint_left]
  constructor
  · intro h x hxS hxK
    exact h hxK hxS
  · intro h x hxK hxS
    exact h x hxS hxK

/-- If `K` is `S`-free, then every point of `S` lies outside the interior of `K`. -/
theorem is_free_of.not_mem_interior
    [TopologicalSpace E]
    {S K : Set E}
    (hK : is_free_of S K)
    {x : E}
    (hxS : x ∈ S) :
    x ∉ interior K :=
  (is_free_of_iff.mp hK) x hxS

/-- A maximal `S`-free convex set is a convex `S`-free set that admits no larger convex
`S`-free superset. -/
def is_maximal_free_of [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    (S : Set E) (K : Set E) : Prop :=
  Convex ℝ K ∧
    is_free_of S K ∧
      ∀ L : Set E, K ⊆ L → Convex ℝ L → is_free_of S L → L = K

/-- `is_maximal_free_of S K` unfolds to convexity, `S`-freeness, and maximality among convex
`S`-free supersets. -/
theorem is_maximal_free_of_iff
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {S K : Set E} :
    is_maximal_free_of S K ↔
      Convex ℝ K ∧
        is_free_of S K ∧
          ∀ L : Set E, K ⊆ L → Convex ℝ L → is_free_of S L → L = K :=
  Iff.rfl

/-- A maximal `S`-free set is convex. -/
theorem is_maximal_free_of.convex
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {S K : Set E}
    (hK : is_maximal_free_of S K) :
    Convex ℝ K :=
  hK.1

/-- A maximal `S`-free set is `S`-free. -/
theorem is_maximal_free_of.free
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {S K : Set E}
    (hK : is_maximal_free_of S K) :
    is_free_of S K :=
  hK.2.1

/-- Maximality among convex `S`-free supersets gives equality with any larger convex `S`-free
superset. -/
theorem is_maximal_free_of.eq_of_subset
    [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    {S K : Set E}
    (hK : is_maximal_free_of S K)
    {L : Set E}
    (hKL : K ⊆ L)
    (hL_convex : Convex ℝ L)
    (hL_free : is_free_of S L) :
    L = K :=
  hK.2.2 L hKL hL_convex hL_free

variable {p : ℕ}

/-- A set `K ⊆ ℝ^p` is lattice-free when its interior contains no point of the embedded lattice
`ℤ^p ⊆ ℝ^p`. -/
def is_lattice_free (K : Set (Fin p → ℝ)) : Prop :=
  is_free_of (ℤ^p) K

/-- A set is lattice-free exactly when no integer vector, viewed in `ℝ^p`, belongs to its
interior. -/
theorem is_lattice_free_iff
    {K : Set (Fin p → ℝ)} :
    is_lattice_free K ↔
      ∀ z : Fin p → ℤ, (Int.cast ∘ z) ∉ interior K := by
  rw [is_lattice_free, is_free_of_iff]
  constructor
  · intro h z
    exact h _ ((mem_integerVectors_iff).2 ⟨z, rfl⟩)
  · intro h x hx
    rcases (mem_integerVectors_iff).1 hx with ⟨z, rfl⟩
    exact h z

/-- If `K` is lattice-free, then every embedded integer point lies outside the interior of `K`. -/
theorem is_lattice_free.not_mem_interior
    {K : Set (Fin p → ℝ)}
    (hK : is_lattice_free K)
    {x : Fin p → ℝ}
    (hx : x ∈ ℤ^p) :
    x ∉ interior K :=
  is_free_of.not_mem_interior hK hx

/-- A maximal lattice-free convex set is a convex lattice-free set that admits no larger convex
lattice-free superset. -/
def is_maximal_lattice_free (K : Set (Fin p → ℝ)) : Prop :=
  is_maximal_free_of (ℤ^p) K

/-- `is_maximal_lattice_free K` unfolds to convexity, lattice-freeness, and maximality among
convex lattice-free supersets. -/
theorem is_maximal_lattice_free_iff
    {K : Set (Fin p → ℝ)} :
    is_maximal_lattice_free K ↔
      Convex ℝ K ∧
        is_lattice_free K ∧
          ∀ L : Set (Fin p → ℝ), K ⊆ L → Convex ℝ L → is_lattice_free L → L = K :=
  Iff.rfl

/-- A maximal lattice-free set is convex. -/
theorem is_maximal_lattice_free.convex
    {K : Set (Fin p → ℝ)}
    (hK : is_maximal_lattice_free K) :
    Convex ℝ K :=
  is_maximal_free_of.convex hK

/-- A maximal lattice-free set is lattice-free. -/
theorem is_maximal_lattice_free.lattice_free
    {K : Set (Fin p → ℝ)}
    (hK : is_maximal_lattice_free K) :
    is_lattice_free K :=
  is_maximal_free_of.free hK

/-- Maximality among convex lattice-free supersets gives equality with any larger convex
lattice-free superset. -/
theorem is_maximal_lattice_free.eq_of_subset
    {K : Set (Fin p → ℝ)}
    (hK : is_maximal_lattice_free K)
    {L : Set (Fin p → ℝ)}
    (hKL : K ⊆ L)
    (hL_convex : Convex ℝ L)
    (hL_lattice_free : is_lattice_free L) :
    L = K :=
  is_maximal_free_of.eq_of_subset hK hKL hL_convex hL_lattice_free

end LatticeFree

/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_proposition_7_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_stable_set_relaxations
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.LinearAlgebra.Pi

open scoped BigOperators

-- Domain sampling for this exercise:
-- * source-facing stable-set owners are reused from `Exercise 7.2`
-- * the graph-relaxation owners `Q`, `FRAC`, and `K` are reused from
--   `ch7_sec7_7_stable_set_relaxations`
-- * the shared support restriction `zero_outside` is reused from `Proposition 7.1`
-- * core/canonical facet owner: Chapter 3's `IsFacetOf`
-- * this file keeps only the exercise-specific support restrictions, graph-support data,
--   and equality-face owners for Exercise 7.19

section Exercise_7_19

variable {V : Type}

variable (G : SimpleGraph V)

/-- The cyclic forward offset from `i` to `j` on `Fin m`, computed modulo `m`. -/
def cyclic_offset {m : ℕ} (i j : Fin m) : ℕ :=
  (j.1 + m - i.1) % m

/-- `cyclic_offset i j` is definitionally the forward modular difference from `i` to `j`. -/
theorem cyclic_offset_eq {m : ℕ} (i j : Fin m) :
    cyclic_offset i j = (j.1 + m - i.1) % m := rfl

/-- A finite cyclic support in the ambient vertex type `V` is an injectively labelled cyclic
vertex set. This is the shared core owner for the cycle, antihole, and web supports below. -/
structure CyclicSupport (V : Type) where
  /-- The number of labelled vertices. -/
  length : ℕ
  /-- The injective cyclic labelling of those vertices. -/
  verts : Fin length ↪ V

/-- A cyclic support can be used as its vertex-labelling map. -/
instance : CoeFun (CyclicSupport V) (fun C ↦ Fin C.length → V) where
  coe C := C.verts

/-- The finite vertex set underlying a cyclic support. -/
def CyclicSupport.vertexFinset (C : CyclicSupport V) : Finset V :=
  Finset.univ.map C.verts

/-- A vertex lies in `C.vertexFinset` exactly when it appears in the cyclic labelling of `C`. -/
theorem CyclicSupport.mem_vertexFinset_iff
    (C : CyclicSupport V) {v : V} :
    v ∈ C.vertexFinset ↔ ∃ i : Fin C.length, C.verts i = v := by
  simp [CyclicSupport.vertexFinset]

/-- A finite cyclic support in the ambient vertex type `V`, represented by an injective cyclic
labelling. -/
structure CycleSupport (V : Type) extends CyclicSupport V where
  /-- A cycle support has at least three vertices. -/
  length_ge_three : 3 ≤ length

/-- A cycle support can be used as its vertex-labelling map. -/
instance : CoeFun (CycleSupport V) (fun C ↦ Fin C.length → V) where
  coe C := C.verts

/-- The finite vertex set underlying a cyclic support. -/
abbrev CycleSupport.vertexFinset (C : CycleSupport V) : Finset V :=
  C.toCyclicSupport.vertexFinset

/-- A vertex lies in `C.vertexFinset` exactly when it appears in the cyclic labelling of `C`. -/
theorem CycleSupport.mem_vertexFinset_iff
    (C : CycleSupport V) {v : V} :
    v ∈ C.vertexFinset ↔ ∃ i : Fin C.length, C.verts i = v := by
  simpa [CycleSupport.vertexFinset] using
    (C.toCyclicSupport.mem_vertexFinset_iff :
      v ∈ C.toCyclicSupport.vertexFinset ↔ ∃ i : Fin C.length, C.verts i = v)

/-- The support `C` is contained in `G` as a cycle when consecutive labelled vertices are
adjacent in `G`. -/
def CycleSupport.IsContainedIn (C : CycleSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i : Fin C.length,
    G.Adj (C.verts i)
      (C.verts
        ⟨(i.1 + 1) % C.length,
          Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) C.length_ge_three)⟩)

/-- `C.IsContainedIn G` means exactly that every consecutive pair in the cyclic order is an edge
of `G`. -/
theorem CycleSupport.isContainedIn_iff
    (C : CycleSupport V) (G : SimpleGraph V) :
    C.IsContainedIn G ↔
      ∀ i : Fin C.length,
        G.Adj (C.verts i)
          (C.verts
            ⟨(i.1 + 1) % C.length,
              Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) C.length_ge_three)⟩) := Iff.rfl

/-- The support `C` is chordless in `G` when the only edges of `G` between cycle vertices are the
cycle edges themselves. -/
def CycleSupport.IsChordlessIn (C : CycleSupport V) (G : SimpleGraph V) : Prop :=
  C.IsContainedIn G ∧
    ∀ i j : Fin C.length, G.Adj (C.verts i) (C.verts j) →
      cyclic_offset i j = 1 ∨ cyclic_offset j i = 1

/-- `C.IsChordlessIn G` unfolds to containing the cycle edges and forbidding extra chords among
the labelled cycle vertices. -/
theorem CycleSupport.isChordlessIn_iff
    (C : CycleSupport V) (G : SimpleGraph V) :
    C.IsChordlessIn G ↔
      C.IsContainedIn G ∧
        ∀ i j : Fin C.length, G.Adj (C.verts i) (C.verts j) →
          cyclic_offset i j = 1 ∨ cyclic_offset j i = 1 := Iff.rfl

/-- The odd-cycle inequality right-hand side attached to a cyclic support is `(length - 1) / 2`.
-/
def odd_cycle_inequality_rhs (C : CycleSupport V) : ℝ :=
  (((C.length - 1) / 2 : ℕ) : ℝ)

/-- `odd_cycle_inequality_rhs C` is the floor-half right-hand side `(|C| - 1) / 2`. -/
theorem odd_cycle_inequality_rhs_eq
    (C : CycleSupport V) :
    odd_cycle_inequality_rhs C = (((C.length - 1) / 2 : ℕ) : ℝ) := rfl

/-- An antihole support in the ambient vertex type `V`, represented by an injective cyclic
labelling. -/
structure AntiholeSupport (V : Type) extends CyclicSupport V where
  /-- An antihole has at least five vertices. -/
  length_ge_five : 5 ≤ length

/-- An antihole support can be used as its vertex-labelling map. -/
instance : CoeFun (AntiholeSupport V) (fun H ↦ Fin H.length → V) where
  coe H := H.verts

/-- The finite vertex set underlying an antihole support. -/
abbrev AntiholeSupport.vertexFinset (H : AntiholeSupport V) : Finset V :=
  H.toCyclicSupport.vertexFinset

/-- A vertex lies in `H.vertexFinset` exactly when it appears in the antihole labelling. -/
theorem AntiholeSupport.mem_vertexFinset_iff
    (H : AntiholeSupport V) {v : V} :
    v ∈ H.vertexFinset ↔ ∃ i : Fin H.length, H.verts i = v := by
  simpa [AntiholeSupport.vertexFinset] using
    (H.toCyclicSupport.mem_vertexFinset_iff :
      v ∈ H.toCyclicSupport.vertexFinset ↔ ∃ i : Fin H.length, H.verts i = v)

/-- The support `H` is contained in `G` as an antihole when every nonconsecutive labelled pair is
an edge of `G`. -/
def AntiholeSupport.IsContainedIn (H : AntiholeSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i j : Fin H.length,
    i ≠ j →
      2 ≤ cyclic_offset i j →
      2 ≤ cyclic_offset j i →
      G.Adj (H.verts i) (H.verts j)

/-- `H.IsContainedIn G` means that each pair prescribed by the antihole pattern is an edge of
`G`. -/
theorem AntiholeSupport.isContainedIn_iff
    (H : AntiholeSupport V) (G : SimpleGraph V) :
    H.IsContainedIn G ↔
      ∀ i j : Fin H.length,
        i ≠ j →
          2 ≤ cyclic_offset i j →
          2 ≤ cyclic_offset j i →
          G.Adj (H.verts i) (H.verts j) := Iff.rfl

/-- The support `H` is induced in `G` as an antihole when the edges of `G` on its labelled
vertices are exactly the antihole edges. -/
def AntiholeSupport.IsInducedIn (H : AntiholeSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i j : Fin H.length,
    G.Adj (H.verts i) (H.verts j) ↔
      i ≠ j ∧ 2 ≤ cyclic_offset i j ∧ 2 ≤ cyclic_offset j i

/-- `H.IsInducedIn G` unfolds to equality between the induced graph on `H.vertexFinset` and the
antihole edge pattern. -/
theorem AntiholeSupport.isInducedIn_iff
    (H : AntiholeSupport V) (G : SimpleGraph V) :
    H.IsInducedIn G ↔
      ∀ i j : Fin H.length,
        G.Adj (H.verts i) (H.verts j) ↔
          i ≠ j ∧ 2 ≤ cyclic_offset i j ∧ 2 ≤ cyclic_offset j i := Iff.rfl

/-- An induced antihole support is automatically contained as an antihole support. -/
theorem AntiholeSupport.IsInducedIn.isContainedIn
    {H : AntiholeSupport V} {G : SimpleGraph V}
    (hInd : H.IsInducedIn G) :
    H.IsContainedIn G := by
  intro i j hij hij₁ hij₂
  exact (hInd i j).2 ⟨hij, hij₁, hij₂⟩

/-- A web support `W_n^k` in the ambient vertex type `V`, represented by an injective cyclic
labelling of the `n` vertices together with the web width `k`. -/
structure WebSupport (V : Type) extends CyclicSupport V where
  /-- The web parameter `k`. -/
  width : ℕ
  /-- The web parameter is positive. -/
  width_pos : 0 < width
  /-- The web condition `2k + 1 ≤ n`. -/
  width_bound : 2 * width + 1 ≤ length

/-- A web support can be used as its vertex-labelling map. -/
instance : CoeFun (WebSupport V) (fun W ↦ Fin W.length → V) where
  coe W := W.verts

/-- The finite vertex set underlying a web support. -/
abbrev WebSupport.vertexFinset (W : WebSupport V) : Finset V :=
  W.toCyclicSupport.vertexFinset

/-- A vertex lies in `W.vertexFinset` exactly when it appears in the web labelling. -/
theorem WebSupport.mem_vertexFinset_iff
    (W : WebSupport V) {v : V} :
    v ∈ W.vertexFinset ↔ ∃ i : Fin W.length, W.verts i = v := by
  simpa [WebSupport.vertexFinset] using
    (W.toCyclicSupport.mem_vertexFinset_iff :
      v ∈ W.toCyclicSupport.vertexFinset ↔ ∃ i : Fin W.length, W.verts i = v)

/-- The support `W` is contained in `G` as a web when every pair whose cyclic distance is at most
`k = W.width` is adjacent in `G`. -/
def WebSupport.IsContainedIn (W : WebSupport V) (G : SimpleGraph V) : Prop :=
  ∀ i j : Fin W.length,
    i ≠ j →
      (cyclic_offset i j ≤ W.width ∨ cyclic_offset j i ≤ W.width) →
      G.Adj (W.verts i) (W.verts j)

/-- `W.IsContainedIn G` means that the edge pattern prescribed by the web parameters occurs in
`G`. -/
theorem WebSupport.isContainedIn_iff
    (W : WebSupport V) (G : SimpleGraph V) :
    W.IsContainedIn G ↔
      ∀ i j : Fin W.length,
        i ≠ j →
          (cyclic_offset i j ≤ W.width ∨ cyclic_offset j i ≤ W.width) →
          G.Adj (W.verts i) (W.verts j) := Iff.rfl

/-- The web inequality right-hand side is `⌊n / (k + 1)⌋`, implemented by natural-number
division. -/
def web_inequality_rhs (W : WebSupport V) : ℝ :=
  ((W.length / (W.width + 1) : ℕ) : ℝ)

/-- `web_inequality_rhs W` is the floor of `n / (k + 1)` for the web parameters of `W`. -/
theorem web_inequality_rhs_eq
    (W : WebSupport V) :
    web_inequality_rhs W = ((W.length / (W.width + 1) : ℕ) : ℝ) := rfl

section Chvatal

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- A Chvatal inequality for the edge relaxation `Q(G)` is given by nonnegative multipliers on
the edge inequalities together with nonnegative slack on the nonnegativity constraints, producing
an integral coefficient vector and the floored aggregated right-hand side. -/
noncomputable def IsEdgeRelaxationChvatalInequality
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) : Prop :=
  ∃ μ : Sym2 V → ℝ, ∃ s : V → ℝ,
    (∀ e : Sym2 V, 0 ≤ μ e) ∧
        (∀ e : Sym2 V, μ e ≠ 0 → e ∈ G.edgeSet) ∧
        (∀ v : V, 0 ≤ s v) ∧
          (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
            (fun v ↦ (∑ e : Sym2 V, if v ∈ e then μ e else 0) - s v) = c ∧
              δ = ((Int.floor (∑ e : Sym2 V, μ e) : ℤ) : ℝ)

/-- `IsEdgeRelaxationChvatalInequality G c δ` unfolds to the existence of nonnegative edge
multipliers and nonnegative slack coefficients yielding the displayed floored inequality. -/
theorem isEdgeRelaxationChvatalInequality_iff
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) :
    IsEdgeRelaxationChvatalInequality G c δ ↔
      ∃ μ : Sym2 V → ℝ, ∃ s : V → ℝ,
        (∀ e : Sym2 V, 0 ≤ μ e) ∧
          (∀ e : Sym2 V, μ e ≠ 0 → e ∈ G.edgeSet) ∧
            (∀ v : V, 0 ≤ s v) ∧
              (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
                (fun v ↦ (∑ e : Sym2 V, if v ∈ e then μ e else 0) - s v) = c ∧
                  δ = ((Int.floor (∑ e : Sym2 V, μ e) : ℤ) : ℝ) := Iff.rfl

/-- A Chvatal inequality for the clique relaxation `K(G)` is given by nonnegative multipliers on
the clique inequalities together with nonnegative slack on the nonnegativity constraints,
producing an integral coefficient vector and the floored aggregated right-hand side. -/
noncomputable def IsCliqueRelaxationChvatalInequality
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) : Prop :=
  ∃ μ : Finset V → ℝ, ∃ s : V → ℝ,
    (∀ K : Finset V, 0 ≤ μ K) ∧
      (∀ K : Finset V, μ K ≠ 0 → G.IsClique K) ∧
        (∀ v : V, 0 ≤ s v) ∧
          (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
            (fun v ↦ (∑ K : Finset V, μ K * (if v ∈ K then 1 else 0)) - s v) = c ∧
              δ = ((Int.floor (∑ K : Finset V, μ K) : ℤ) : ℝ)

/-- `IsCliqueRelaxationChvatalInequality G c δ` unfolds to the existence of nonnegative clique
multipliers and nonnegative slack coefficients yielding the displayed floored inequality. -/
theorem isCliqueRelaxationChvatalInequality_iff
    (G : SimpleGraph V) (c : V → ℝ) (δ : ℝ) :
    IsCliqueRelaxationChvatalInequality G c δ ↔
      ∃ μ : Finset V → ℝ, ∃ s : V → ℝ,
        (∀ K : Finset V, 0 ≤ μ K) ∧
        (∀ K : Finset V, μ K ≠ 0 → G.IsClique K) ∧
          (∀ v : V, 0 ≤ s v) ∧
            (∀ v : V, ∃ z : ℤ, c v = (z : ℝ)) ∧
                (fun v ↦ (∑ K : Finset V, μ K * (if v ∈ K then 1 else 0)) - s v) = c ∧
                  δ = ((Int.floor (∑ K : Finset V, μ K) : ℤ) : ℝ) := Iff.rfl

end Chvatal

/-- Dotting `stableSetIndicator S` with `x` recovers the coordinate sum over `S`. -/
theorem stableSetIndicator_dotProduct [Fintype V]
    (S : Finset V) (x : V → ℝ) :
    stableSetIndicator S ⬝ᵥ x = S.sum x := by
  classical
  simp [dotProduct, stableSetIndicator, Finset.sum_ite_mem]

/-- The equality face of `STAB(G)` cut out by the clique inequality on `K`. -/
noncomputable abbrev cliqueFace [Fintype V] (G : SimpleGraph V) (K : Finset V) : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∧ K.sum x = 1}

/-- Membership in `cliqueFace G K` means belonging to `STAB(G)` and satisfying the clique
equation on `K`. -/
theorem mem_cliqueFace_iff [Fintype V]
    (G : SimpleGraph V) (K : Finset V) (x : V → ℝ) :
    x ∈ cliqueFace G K ↔ x ∈ STAB(G) ∧ K.sum x = 1 := by
  rfl

/-- The equality face cut out on the support restriction of `STAB(G)` by the odd-cycle
inequality attached to `C`. -/
noncomputable abbrev oddCycleFace [Fintype V]
    (G : SimpleGraph V) (C : CycleSupport V) : Set (V → ℝ) :=
  {x |
    x ∈ STAB(G) ∩ zero_outside C.vertexFinset ∧
      C.vertexFinset.sum x = odd_cycle_inequality_rhs C}

/-- Membership in `oddCycleFace G C` means belonging to the support restriction of `STAB(G)` and
satisfying the odd-cycle equality on `C.vertexFinset`. -/
theorem mem_oddCycleFace_iff [Fintype V]
    (G : SimpleGraph V) (C : CycleSupport V) (x : V → ℝ) :
    x ∈ oddCycleFace G C ↔
      x ∈ STAB(G) ∩ zero_outside C.vertexFinset ∧
        C.vertexFinset.sum x = odd_cycle_inequality_rhs C := by
  rfl

/-- The equality face cut out on the support restriction of `STAB(G)` by the antihole
inequality attached to `H`. -/
noncomputable abbrev antiholeFace [Fintype V]
    (G : SimpleGraph V) (H : AntiholeSupport V) : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∩ zero_outside H.vertexFinset ∧ H.vertexFinset.sum x = 2}

/-- Membership in `antiholeFace G H` means belonging to the support restriction of `STAB(G)` and
satisfying the antihole equality on `H.vertexFinset`. -/
theorem mem_antiholeFace_iff [Fintype V]
    (G : SimpleGraph V) (H : AntiholeSupport V) (x : V → ℝ) :
    x ∈ antiholeFace G H ↔
      x ∈ STAB(G) ∩ zero_outside H.vertexFinset ∧
        H.vertexFinset.sum x = 2 := by
  rfl

/-- Helper for Exercise 7.19: the coordinate-zero equality face of `STAB(G)` at the vertex `v`.
-/
noncomputable abbrev coordinateZeroFace [Fintype V]
    (G : SimpleGraph V) (v : V) : Set (V → ℝ) :=
  {x | x ∈ STAB(G) ∧ x v = 0}

/-- Helper for Exercise 7.19: membership in `coordinateZeroFace G v` means belonging to `STAB(G)`
and vanishing at the coordinate `v`. -/
theorem mem_coordinateZeroFace_iff [Fintype V]
    (G : SimpleGraph V) (v : V) (x : V → ℝ) :
    x ∈ coordinateZeroFace G v ↔ x ∈ STAB(G) ∧ x v = 0 := by
  rfl

section CliqueFacetHelpers

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V
noncomputable local instance : DecidableRel G.Adj := Classical.decRel G.Adj

/-- Helper for Exercise 7.19: the empty stable set contributes the zero vector. -/
private lemma stableSetIndicatorEmpty :
    stableSetIndicator (∅ : Finset V) = 0 := by
  -- Every coordinate of the empty indicator vanishes.
  ext v
  simp [stableSetIndicator]

/-- Helper for Exercise 7.19: singleton stable sets give coordinate unit vectors. -/
private lemma stableSetIndicatorSingleton (v : V) :
    stableSetIndicator ({v} : Finset V) = Pi.single v 1 := by
  -- The singleton indicator is `1` at `v` and `0` away from `v`.
  ext u
  by_cases huv : u = v
  · subst huv
    simp [stableSetIndicator]
  · simp [stableSetIndicator, huv]

/-- Helper for Exercise 7.19: a two-point indicator splits into the two singleton coordinates. -/
private lemma stableSetIndicatorPairOfNe {u v : V} (huv : u ≠ v) :
    stableSetIndicator ({u, v} : Finset V) = Pi.single u 1 + Pi.single v 1 := by
  -- The two support coordinates contribute `1`, and every other coordinate contributes `0`.
  ext w
  by_cases hwu : w = u
  · subst hwu
    simp [stableSetIndicator, huv]
  · by_cases hwv : w = v
    · subst hwv
      simp [stableSetIndicator, hwu]
    · simp [stableSetIndicator, hwu, hwv]

/-- Helper for Exercise 7.19: `0` together with the coordinate unit vectors is affinely
independent in `ℝ^V`. -/
private lemma affineIndependentNoneOrSingle :
    AffineIndependent ℝ
      (fun o : Option V ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v 1)) := by
  classical
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v 1)
  let e : {o : Option V // o ≠ none} → V := fun o ↦
    match o with
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some v, _⟩ => v
  have he_injective : Function.Injective e := by
    intro a b hab
    rcases a with ⟨oa, hoa⟩
    rcases b with ⟨ob, hob⟩
    cases oa with
    | none => exact False.elim (hoa rfl)
    | some va =>
        cases ob with
        | none => exact False.elim (hob rfl)
        | some vb =>
            simp only [ne_eq] at hab
            subst hab
            rfl
  -- Affine independence reduces to linear independence of the standard basis.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p none]
  have hvsub :
      (fun i : {o : Option V // o ≠ none} ↦ (p i -ᵥ p none : V → ℝ)) =
        fun i : {o : Option V // o ≠ none} ↦ Pi.single (e i) 1 := by
    funext i
    rcases i with ⟨o, ho⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some v =>
        simp [p, e, vsub_eq_sub]
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp e he_injective

/-- Helper for Exercise 7.19: the stable-set polytope spans the whole ambient function space. -/
private theorem stableSetPolytopeAffineSpanEqTop :
    affineSpan ℝ STAB(G) = ⊤ := by
  classical
  let p : Option V → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun v ↦ Pi.single v 1)
  have hp : Set.range p ⊆ STAB(G) := by
    intro x hx
    rcases hx with ⟨o, rfl⟩
    cases o with
    | none =>
        -- The origin comes from the empty stable set.
        have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
        simpa [p, stableSetIndicatorEmpty] using h0
    | some v =>
        -- Each singleton indicator is also a stable-set vertex.
        have hv : stableSetIndicator ({v} : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
        simpa [p, stableSetIndicatorSingleton] using hv
  have hp_affine : AffineIndependent ℝ p := by
    -- The chosen family is exactly the origin plus the coordinate unit vectors.
    simpa [p] using (affineIndependentNoneOrSingle (V := V))
  have htop : affineSpan ℝ (Set.range p) = ⊤ := by
    -- The family has `|V| + 1` points in an ambient space of dimension `|V|`.
    have hcard : Fintype.card (Option V) = Fintype.card V + 1 := by
      simp
    exact hp_affine.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hcard)
  have hmono : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ STAB(G) :=
    affineSpan_mono ℝ hp
  -- A superset of a spanning affine family has full affine span.
  exact top_unique (by simpa [htop] using hmono)

/-- Helper for Exercise 7.19: a nonzero linear functional on `ℝ^V` has codimension-one kernel. -/
private lemma finrankKerEqCardSubOne {L : (V → ℝ) →ₗ[ℝ] ℝ}
    (hL : L ≠ 0) :
    Module.finrank ℝ (LinearMap.ker L) = Fintype.card V - 1 := by
  let f : Module.Dual ℝ (V → ℝ) := L
  have hf : f ≠ 0 := by
    simpa [f] using hL
  have hker_add_one :
      Module.finrank ℝ (LinearMap.ker L) + 1 = Fintype.card V := by
    simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
  exact Nat.eq_sub_of_add_eq hker_add_one

/-- Helper for Exercise 7.19: the coefficient vector `c` defines the dot-product functional
`x ↦ c ⬝ᵥ x`. -/
private def stableSetDotProductLinearMap (c : V → ℝ) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ v, c v • LinearMap.proj v

/-- Helper for Exercise 7.19: `stableSetDotProductLinearMap c` evaluates as `c ⬝ᵥ x`. -/
private lemma stableSetDotProductLinearMap_apply (c x : V → ℝ) :
    stableSetDotProductLinearMap c x = c ⬝ᵥ x := by
  -- The linear map was defined coordinatewise as the dot product with `c`.
  simp [stableSetDotProductLinearMap, dotProduct]

/-- Helper for Exercise 7.19: a nonempty valid equality slice is exposed. -/
  private lemma equalitySetIsExposed
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ P → c ⬝ᵥ x ≤ δ)
    (hx₀ : x₀ ∈ P)
    (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    IsExposed ℝ P {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} := by
  have hvalid' : ∀ ⦃x : V → ℝ⦄, x ∈ P → stableSetDotProductLinearMap c x ≤ δ := by
    intro x hx
    simpa [stableSetDotProductLinearMap_apply] using hvalid hx
  have hEq :
      {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ} =
        (⟨stableSetDotProductLinearMap c,
          (stableSetDotProductLinearMap c).continuous_of_finiteDimensional⟩ :
          (V → ℝ) →L[ℝ] ℝ).toExposed P := by
    ext x
    constructor
    · rintro ⟨hxP, hxEq⟩
      refine ⟨hxP, fun y hyP ↦ ?_⟩
      calc
        stableSetDotProductLinearMap c y ≤ δ := hvalid' hyP
        _ = stableSetDotProductLinearMap c x := by
              simpa [stableSetDotProductLinearMap_apply] using hxEq.symm
    · intro hx
      refine ⟨hx.1, ?_⟩
      have hx₀_le :
          stableSetDotProductLinearMap c x₀ ≤ stableSetDotProductLinearMap c x :=
        hx.2 x₀ hx₀
      have hx_le :
          stableSetDotProductLinearMap c x ≤ stableSetDotProductLinearMap c x₀ := by
        simpa [stableSetDotProductLinearMap_apply, hx₀_eq] using hvalid' hx.1
      -- The exposing functional is constant on the equality slice.
      have hmap_eq :
          stableSetDotProductLinearMap c x = stableSetDotProductLinearMap c x₀ :=
        le_antisymm hx_le hx₀_le
      simpa [stableSetDotProductLinearMap_apply, hx₀_eq] using hmap_eq
  rw [hEq]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 7.19: the direction of a tight equality slice lies in the kernel of its
defining linear functional. -/
private lemma equalitySetDirectionLeKer
    {P : Set (V → ℝ)} {c x₀ : V → ℝ} {δ : ℝ}
    (hx₀_eq : c ⬝ᵥ x₀ = δ) :
    (affineSpan ℝ {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}).direction ≤
      LinearMap.ker (stableSetDotProductLinearMap c) := by
  let F : Set (V → ℝ) := {x : V → ℝ | x ∈ P ∧ c ⬝ᵥ x = δ}
  let H : AffineSubspace ℝ (V → ℝ) :=
    AffineSubspace.mk' x₀ (LinearMap.ker (stableSetDotProductLinearMap c))
  have hF_le_H : F ⊆ H := by
    intro x hx
    change x ∈ H
    rw [AffineSubspace.mem_mk']
    refine LinearMap.mem_ker.2 ?_
    rcases hx with ⟨-, hx_eq⟩
    simp [stableSetDotProductLinearMap_apply, vsub_eq_sub, hx_eq, hx₀_eq]
  have h_aff_le : affineSpan ℝ F ≤ H := (affineSpan_le).2 hF_le_H
  -- Passing to directions identifies the ambient affine subspace with the kernel.
  simpa [H] using
    (AffineSubspace.direction_le h_aff_le :
      (affineSpan ℝ F).direction ≤ H.direction)

/-- Helper for Exercise 7.19: if a dot-product inequality holds on all stable-set vertices, it
holds on the whole stable-set polytope. -/
private lemma dotProductLeOfMemStableSetPolytope
    {c : V → ℝ} {δ : ℝ}
    (hvertex : ∀ s : Finset V, G.IsIndepSet s → c ⬝ᵥ stableSetIndicator s ≤ δ)
    {x : V → ℝ} (hx : x ∈ STAB(G)) :
    c ⬝ᵥ x ≤ δ := by
  let H : Set (V → ℝ) := {y : V → ℝ | c ⬝ᵥ y ≤ δ}
  have hconvex : Convex ℝ H := by
    -- A dot-product inequality cuts out a linear halfspace.
    simpa [H, stableSetDotProductLinearMap_apply] using
      convex_halfSpace_le (stableSetDotProductLinearMap c).isLinear δ
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact hvertex s hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- Helper for Exercise 7.19: every point of `STAB(G)` has nonnegative coordinates. -/
private lemma coordinateNonneg_on_stableSetPolytope (v : V) {x : V → ℝ}
    (hx : x ∈ STAB(G)) :
    0 ≤ x v := by
  have hvalid :
      (-Pi.single v (1 : ℝ) : V → ℝ) ⬝ᵥ x ≤ 0 :=
    dotProductLeOfMemStableSetPolytope (G := G)
      (c := -Pi.single v (1 : ℝ)) (δ := 0)
      (hvertex := by
        intro s hs
        by_cases hv : v ∈ s
        · simp [stableSetIndicator, hv, dotProduct]
        · simp [stableSetIndicator, hv, dotProduct]) hx
  simpa [dotProduct, Pi.single_apply] using hvalid

/-- Helper for Exercise 7.19: `cliqueLinearMap K` is the linear functional `x ↦ ∑_{u ∈ K} x u`. -/
private def cliqueLinearMap (K : Finset V) : (V → ℝ) →ₗ[ℝ] ℝ :=
  ∑ u ∈ K, LinearMap.proj u

/-- Helper for Exercise 7.19: `cliqueLinearMap K` evaluates as `K.sum x`. -/
private lemma cliqueLinearMap_apply (K : Finset V) (x : V → ℝ) :
    cliqueLinearMap K x = K.sum x := by
  -- The clique functional is the coordinate sum over `K`.
  simp [cliqueLinearMap]

/-- Helper for Exercise 7.19: a stable set meets a clique in at most one vertex. -/
private lemma clique_sum_stableSetIndicator_le_one
    {K s : Finset V} (hK : G.IsClique K) (hs : G.IsIndepSet s) :
    K.sum (fun v ↦ stableSetIndicator s v) ≤ 1 := by
  have hsum :
      K.sum (fun v ↦ stableSetIndicator s v) = ((K.filter fun v ↦ v ∈ s).card : ℝ) := by
    -- Summing the `0/1` coordinates counts the clique vertices that lie in `s`.
    simp [stableSetIndicator, Finset.filter_mem_eq_inter]
  have hcard : (K.filter fun v ↦ v ∈ s).card ≤ 1 := by
    -- Two distinct vertices in the intersection would be both adjacent and nonadjacent.
    refine Finset.card_le_one_iff.2 ?_
    intro a b ha hb
    by_contra hab
    have haK : a ∈ K := (Finset.mem_filter.mp ha).1
    have hbK : b ∈ K := (Finset.mem_filter.mp hb).1
    have has : a ∈ s := (Finset.mem_filter.mp ha).2
    have hbs : b ∈ s := (Finset.mem_filter.mp hb).2
    exact (hs has hbs hab) (hK haK hbK hab)
  rw [hsum]
  exact_mod_cast hcard

/-- Helper for Exercise 7.19: clique inequalities are valid on the stable-set polytope. -/
private lemma clique_sum_le_one_of_mem_stableSetPolytope
    (K : Finset V) (hK : G.IsClique K) {x : V → ℝ}
    (hx : x ∈ STAB(G)) :
    K.sum x ≤ 1 := by
  let H : Set (V → ℝ) := {y : V → ℝ | K.sum y ≤ 1}
  have hconvex : Convex ℝ H := by
    -- The target set is a linear half-space.
    simpa [H, cliqueLinearMap_apply] using
      convex_halfSpace_le (cliqueLinearMap K).isLinear (1 : ℝ)
  have hsubset : convexHull ℝ (stableSetVertices G) ⊆ H := by
    refine convexHull_min ?_ hconvex
    intro y hy
    rw [mem_stableSetVertices_iff] at hy
    rcases hy with ⟨s, hs, rfl⟩
    exact clique_sum_stableSetIndicator_le_one (G := G) hK hs
  rw [stableSetPolytope_eq_convexHull] at hx
  exact hsubset hx

/-- Helper for Exercise 7.19: every vertex outside a maximal clique has a nonneighbor inside that
clique. -/
private lemma maximalCliqueExistsNonadjacentMem
    {K : Finset V} {v : V} (hK : Maximal G.IsClique K) (hv : v ∉ K) :
    ∃ w ∈ K, ¬ G.Adj v w := by
  by_contra h
  have hclique : G.IsClique K := hK.prop
  have hv_adj : ∀ w ∈ K, G.Adj v w := by
    intro w hw
    by_contra hvw
    exact h ⟨w, hw, hvw⟩
  have hinsert : G.IsClique (insert v (↑K : Set V)) := by
    rw [SimpleGraph.isClique_insert_of_notMem]
    · exact ⟨hclique, fun w hw ↦ hv_adj w hw⟩
    · simpa using hv
  exact hv (hK.mem_of_prop_insert hinsert)

/-- Helper for Exercise 7.19: the stable-set witness family attached to a maximal clique is
linearly independent. -/
private lemma cliqueWitnessLinearIndependent
    {K : Finset V} {W : V → Finset V}
    (h_singleton : ∀ v, v ∈ K → W v = {v})
    (h_mem : ∀ v, v ∉ K → v ∈ W v)
    (h_pair : ∀ v, v ∉ K → ∃ w ∈ K, W v = {v, w}) :
    LinearIndependent ℝ (fun v ↦ stableSetIndicator (W v)) := by
  rw [linearIndependent_iff']
  intro s g hsum v hv
  have hOutside : ∀ u ∈ s, u ∉ K → g u = 0 := by
    intro u hu huK
    have hcoord : ∑ t ∈ s, g t • stableSetIndicator (W t) u = 0 := by
      -- Evaluate the dependence relation at the outside coordinate `u`.
      simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hsum u
    have hrest : ∀ t ∈ s, t ≠ u → g t • stableSetIndicator (W t) u = 0 := by
      intro t ht htu
      by_cases htK : t ∈ K
      · -- Clique witnesses contribute only on their own coordinate.
        rw [h_singleton t htK]
        simp [stableSetIndicator, htu.symm]
      · -- A distinct outside witness contributes only on its own outside coordinate.
        obtain ⟨w, hwK, hpair⟩ := h_pair t htK
        have huw : u ≠ w := by
          intro huw
          exact huK (huw ▸ hwK)
        rw [hpair, stableSetIndicatorPairOfNe (by
          intro htw
          exact htK (htw ▸ hwK))]
        simp [htu, huw]
    rw [Finset.sum_eq_single_of_mem u hu hrest] at hcoord
    have hself : stableSetIndicator (W u) u = 1 := by
      -- The witness for an outside vertex contains that vertex.
      rw [stableSetIndicator]
      exact if_pos (h_mem u huK)
    simpa [hself] using hcoord
  by_cases hKv : v ∈ K
  · have hcoord : ∑ t ∈ s, g t • stableSetIndicator (W t) v = 0 := by
      -- Evaluate at the clique coordinate `v`.
      simpa [Finset.sum_apply, Pi.smul_apply] using congrFun hsum v
    have hrest : ∀ t ∈ s, t ≠ v → g t • stableSetIndicator (W t) v = 0 := by
      intro t ht htv
      by_cases htK : t ∈ K
      · rw [h_singleton t htK]
        simp [stableSetIndicator, htv.symm]
      · rw [hOutside t ht htK, zero_smul]
    rw [Finset.sum_eq_single_of_mem v hv hrest] at hcoord
    have hself : stableSetIndicator (W v) v = 1 := by
      -- The clique witness at `v` is exactly `{v}`.
      rw [h_singleton v hKv]
      simp [stableSetIndicator]
    simpa [hself] using hcoord
  · exact hOutside v hv hKv

/-- Helper for Exercise 7.19: a maximal clique yields `|V|` affinely independent tight stable-set
witnesses for its clique face. -/
private theorem maximalCliqueWitnessFamily
    {K : Finset V} (hK : Maximal G.IsClique K) :
    ∃ W : V → Finset V,
      (∀ v, G.IsIndepSet (W v)) ∧
      (∀ v, K.sum (fun u ↦ stableSetIndicator (W v) u) = 1) ∧
      AffineIndependent ℝ (fun v ↦ stableSetIndicator (W v)) := by
  have hpartner :
      ∀ v, v ∉ K → ∃ w ∈ K, ¬ G.Adj v w := fun v hv ↦
        maximalCliqueExistsNonadjacentMem (G := G) hK hv
  choose partner partner_mem partner_nonadj using hpartner
  let witnessSets : V → Finset V := fun v ↦
    if hv : v ∈ K then {v} else {v, partner v hv}
  have hsingle : ∀ v, v ∈ K → witnessSets v = {v} := by
    intro v hv
    simp [witnessSets, hv]
  have hmem : ∀ v, v ∉ K → v ∈ witnessSets v := by
    intro v hv
    simp [witnessSets, hv]
  have hpair : ∀ v, v ∉ K → ∃ w ∈ K, witnessSets v = {v, w} := by
    intro v hv
    refine ⟨partner v hv, partner_mem v hv, ?_⟩
    simp [witnessSets, hv]
  have hindep : ∀ u, G.IsIndepSet (witnessSets u) := by
    intro u
    by_cases hu : u ∈ K
    · -- Clique vertices contribute singleton stable sets.
      rw [hsingle u hu]
      simp
    · -- Outside vertices are paired with a nonneighbor in the clique.
      have hneq : u ≠ partner u hu := by
        intro hEq
        exact hu (hEq ▸ partner_mem u hu)
      have hnotAdj : ¬ G.Adj u (partner u hu) := partner_nonadj u hu
      rw [show witnessSets u = {u, partner u hu} by simp [witnessSets, hu]]
      rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      simp at ha hb
      rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
      · exact False.elim (hab rfl)
      · exact hnotAdj
      · simpa [SimpleGraph.adj_comm] using hnotAdj
      · exact False.elim (hab rfl)
  have htight : ∀ v, K.sum (fun u ↦ stableSetIndicator (witnessSets v) u) = 1 := by
    intro v
    by_cases hv : v ∈ K
    · -- A clique singleton hits the clique sum exactly once.
      rw [hsingle v hv, stableSetIndicatorSingleton]
      simp [hv]
    · -- An outside witness contributes only through its chosen clique partner.
      have hneq : v ≠ partner v hv := by
        intro hEq
        exact hv (hEq ▸ partner_mem v hv)
      rw [show witnessSets v = {v, partner v hv} by simp [witnessSets, hv]]
      rw [stableSetIndicatorPairOfNe hneq]
      simp [Finset.sum_add_distrib, hv, partner_mem v hv]
  refine ⟨witnessSets, hindep, htight, ?_⟩
  -- Linear independence of the witness vectors implies affine independence.
  exact (cliqueWitnessLinearIndependent hsingle hmem hpair).affineIndependent

/-- Helper for Exercise 7.19: the coordinate-zero face at `v` contains the origin and the
singleton indicators away from `v`. -/
private lemma coordinateZeroFaceAffineIndependentFamily (v : V) :
    AffineIndependent ℝ
      (fun o : Option {u : V // u ≠ v} ↦
        Option.elim o (0 : V → ℝ) (fun u ↦ Pi.single u.1 1)) := by
  let U := {u : V // u ≠ v}
  let p : Option U → V → ℝ :=
    fun o ↦ Option.elim o (0 : V → ℝ) (fun u ↦ Pi.single u.1 1)
  let e : {o : Option U // o ≠ none} → U := fun o ↦
    match o with
    | ⟨none, hnone⟩ => False.elim (hnone rfl)
    | ⟨some u, _⟩ => u
  have he_injective : Function.Injective e := by
    intro a b hab
    rcases a with ⟨oa, hoa⟩
    rcases b with ⟨ob, hob⟩
    cases oa with
    | none => exact False.elim (hoa rfl)
    | some ua =>
        cases ob with
        | none => exact False.elim (hob rfl)
        | some ub =>
            simp only [ne_eq] at hab
            subst hab
            rfl
  have hcomp_injective : Function.Injective (fun i : {o : Option U // o ≠ none} ↦ (e i).1) := by
    intro a b hab
    apply he_injective
    exact Subtype.ext hab
  -- Affine independence again reduces to standard basis vectors.
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p none]
  have hvsub :
      (fun i : {o : Option U // o ≠ none} ↦ (p i -ᵥ p none : V → ℝ)) =
        fun i : {o : Option U // o ≠ none} ↦ Pi.single (e i).1 1 := by
    funext i
    rcases i with ⟨o, ho⟩
    cases o with
    | none => exact False.elim (ho rfl)
    | some u =>
        simp [p, e, vsub_eq_sub]
  rw [hvsub]
  exact (Pi.linearIndependent_single_one V ℝ).comp _ hcomp_injective

/-- Helper for Exercise 7.19: the coordinate-zero face of `STAB(G)` is itself a facet. -/
private theorem coordinateZeroFace_isFacetOf [Nonempty V] (v : V) :
    IsFacetOf STAB(G) (coordinateZeroFace G v) := by
  let F : Set (V → ℝ) := coordinateZeroFace G v
  have hzero_mem : (0 : V → ℝ) ∈ F := by
    -- The empty stable set witnesses nonemptiness of the face.
    rw [mem_coordinateZeroFace_iff]
    refine ⟨?_, by simp⟩
    have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
      stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
    simpa [stableSetIndicatorEmpty] using h0
  have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → (-Pi.single v (1 : ℝ) : V → ℝ) ⬝ᵥ x ≤ 0 := by
    intro x hx
    have hxv : 0 ≤ x v := coordinateNonneg_on_stableSetPolytope (G := G) v hx
    simpa [dotProduct, Pi.single_apply] using (neg_nonpos.mpr hxv)
  have hF_exposed : IsExposed ℝ STAB(G) F := by
    -- The coordinate-zero slice is the equality case of the valid nonnegativity inequality.
    have hEq :
        F = {x : V → ℝ | x ∈ STAB(G) ∧ (-Pi.single v (1 : ℝ) : V → ℝ) ⬝ᵥ x = 0} := by
      ext x
      simp [F, coordinateZeroFace, dotProduct, Pi.single_apply]
    have hzero_stab : (0 : V → ℝ) ∈ STAB(G) :=
      (mem_coordinateZeroFace_iff G v 0).1 hzero_mem |>.1
    rw [hEq]
    exact equalitySetIsExposed hvalid hzero_stab (by simp)
  have hdir_le :
      (affineSpan ℝ F).direction ≤ LinearMap.ker (LinearMap.proj v) := by
    -- Differences of tight points preserve the vanishing `v`-coordinate.
    have hEq :
        F = {x : V → ℝ | x ∈ STAB(G) ∧ (Pi.single v (1 : ℝ)) ⬝ᵥ x = 0} := by
      ext x
      simp [F, coordinateZeroFace, dotProduct, Pi.single_apply]
    rw [hEq]
    simpa [stableSetDotProductLinearMap, dotProduct] using
      (equalitySetDirectionLeKer
        (P := STAB(G)) (c := Pi.single v (1 : ℝ)) (x₀ := 0) (δ := 0) (by simp) :
          (affineSpan ℝ {x : V → ℝ | x ∈ STAB(G) ∧ (Pi.single v (1 : ℝ)) ⬝ᵥ x = 0}).direction ≤
            LinearMap.ker (stableSetDotProductLinearMap (Pi.single v (1 : ℝ))))
  have hface_dim_lower :
      Fintype.card V - 1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
    let U := {u : V // u ≠ v}
    let p : Option U → V → ℝ :=
      fun o ↦ Option.elim o (0 : V → ℝ) (fun u ↦ Pi.single u.1 1)
    have hp_mem : Set.range p ⊆ F := by
      intro x hx
      rcases hx with ⟨o, rfl⟩
      cases o with
      | none =>
          simpa [F, p] using hzero_mem
      | some u =>
          have hu : stableSetIndicator ({u.1} : Finset V) ∈ STAB(G) :=
            stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
          have huFace : (Pi.single u.1 (1 : ℝ) : V → ℝ) ∈ coordinateZeroFace G v := by
            rw [mem_coordinateZeroFace_iff]
            refine ⟨?_, ?_⟩
            · simpa [stableSetIndicatorSingleton] using hu
            · simp [Pi.single_apply, u.2]
          simpa [F, p] using huFace
    have hp_affine : AffineIndependent ℝ p := by
      simpa [p] using coordinateZeroFaceAffineIndependentFamily (V := V) v
    have hp_dim :
        Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = Fintype.card V - 1 := by
      have hsubtype_card :
          Fintype.card U = Fintype.card V - 1 := by
        simpa [U] using (Fintype.card_subtype_compl (p := fun u : V ↦ u = v))
      have hcard : Fintype.card (Option U) = Fintype.card V := by
        calc
          Fintype.card (Option U) = Fintype.card U + 1 := by simp
          _ = (Fintype.card V - 1) + 1 := by rw [hsubtype_card]
          _ = Fintype.card V := by
            exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
      rw [direction_affineSpan]
      exact hp_affine.finrank_vectorSpan <| by
        simpa [hcard] using (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
    have hspan_le : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ F :=
      affineSpan_mono ℝ hp_mem
    simpa [hp_dim] using Submodule.finrank_mono (AffineSubspace.direction_le hspan_le)
  have hproj_ne : (LinearMap.proj v : (V → ℝ) →ₗ[ℝ] ℝ) ≠ 0 := by
    intro hzero
    have hEval := congrArg (fun L : (V → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single v 1)) hzero
    simp at hEval
  have hface_dim_upper :
      Module.finrank ℝ (affineSpan ℝ F).direction ≤ Fintype.card V - 1 := by
    simpa [finrankKerEqCardSubOne (V := V) hproj_ne] using Submodule.finrank_mono hdir_le
  have hpoly_dim :
      Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
    rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
      finrank_top, Module.finrank_fintype_fun_eq_card]
  rw [isFacetOf_iff]
  refine ⟨⟨0, hzero_mem⟩, hF_exposed, ?_⟩
  have hface_dim :
      Module.finrank ℝ (affineSpan ℝ F).direction = Fintype.card V - 1 :=
    le_antisymm hface_dim_upper hface_dim_lower
  calc
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 = Fintype.card V := by
      rw [hface_dim]
      exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
    _ = Module.finrank ℝ (affineSpan ℝ STAB(G)).direction := hpoly_dim.symm

/-- Helper for Exercise 7.19: in a full-dimensional ambient polytope, two facets coincide as soon
as one is contained in the other. -/
private lemma facet_eq_of_subset
    {P F H : Set (V → ℝ)}
    (hP_dim : Module.finrank ℝ (affineSpan ℝ P).direction = Fintype.card V)
    (hF : IsFacetOf P F)
    (hH : IsFacetOf P H)
    (hsubset : F ⊆ H) :
    F = H := by
  rcases hF with ⟨hF_nonempty, hF_exposed, hF_codim⟩
  rcases hH with ⟨hH_nonempty, hH_exposed, hH_codim⟩
  obtain ⟨xF, hxF⟩ := hF_nonempty
  have hxFH : xF ∈ H := hsubset hxF
  have hdim_eq :
      Module.finrank ℝ (affineSpan ℝ F).direction =
        Module.finrank ℝ (affineSpan ℝ H).direction := by
    omega
  have h_aff_le : affineSpan ℝ F ≤ affineSpan ℝ H := affineSpan_mono ℝ hsubset
  have hdir_eq :
      (affineSpan ℝ F).direction = (affineSpan ℝ H).direction := by
    exact Submodule.eq_of_le_of_finrank_eq (AffineSubspace.direction_le h_aff_le) hdim_eq
  have hspan_eq :
      affineSpan ℝ F = affineSpan ℝ H := by
    -- Equal directions and a common point identify the two affine spans.
    refine (AffineSubspace.eq_iff_direction_eq_of_mem
      (subset_affineSpan ℝ _ hxF) (subset_affineSpan ℝ _ hxFH)).2 hdir_eq
  obtain ⟨l, hF_eq⟩ := hF_exposed ⟨xF, hxF⟩
  have hxF_face : xF ∈ l.toExposed P := by
    simpa [hF_eq] using hxF
  have hxF_mem : xF ∈ P := hxF_face.1
  have hxF_max : ∀ y, y ∈ P → l y ≤ l xF := hxF_face.2
  have hlevel : ∀ ⦃x : V → ℝ⦄, x ∈ F → l x = l xF := by
    intro x hx
    have hx_face : x ∈ l.toExposed P := by
      simpa [hF_eq] using hx
    exact le_antisymm (hxF_max x hx_face.1) (hx_face.2 xF hxF_mem)
  have hlevel_aff :
      ∀ ⦃x : V → ℝ⦄, x ∈ affineSpan ℝ F → l x = l xF := by
    intro x hx
    refine affineSpan_induction (k := ℝ) (s := F) (p := fun y : V → ℝ ↦ l y = l xF) hx ?_ ?_
    · intro y hy
      exact hlevel hy
    · intro c u v w hu hv hw
      -- The exposing functional stays constant on the whole affine span of `F`.
      change l (c • (u - v) + w) = l xF
      calc
        l (c • (u - v) + w) = c * (l u - l v) + l w := by
            simp [map_add, map_sub]
        _ = l xF := by
            simp [hu, hv, hw]
  ext x
  constructor
  · intro hx
    exact hsubset hx
  · intro hx
    have hx_aff : x ∈ affineSpan ℝ F := by
      simpa [hspan_eq] using subset_affineSpan ℝ H hx
    have hx_level : l x = l xF := hlevel_aff hx_aff
    have hx_exposed : x ∈ l.toExposed P := by
      refine ⟨hH_exposed.subset hx, ?_⟩
      intro y hy
      calc
        l y ≤ l xF := hxF_max y hy
        _ = l x := hx_level.symm
    simpa [hF_eq] using hx_exposed

end CliqueFacetHelpers

section SupportedFacetHelpers

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Helper for Exercise 7.19: vectors supported on `S` are exactly the coordinate subspace
`Pi.spanSubset ℝ S`. -/
private lemma mem_supportSpanSubset_iff
    (S : Finset V) (x : V → ℝ) :
    x ∈ Pi.spanSubset ℝ (↑S : Set V) ↔ ∀ v, v ∉ S → x v = 0 := by
  -- `Pi.spanSubset` is the canonical supported-coordinate subspace for the finite support `S`.
  rw [Pi.mem_spanSubset_iff]
  constructor
  · intro hx v hv
    exact hx v (by simpa using hv)
  · intro hx v hv
    exact hx v (by simpa using hv)

/-- Helper for Exercise 7.19: the support restriction `zero_outside S` lies in the canonical
supported-coordinate subspace. -/
private lemma zeroOutside_subset_supportSpanSubset
    (S : Finset V) :
    zero_outside S ⊆ (Pi.spanSubset ℝ (↑S : Set V) : Set (V → ℝ)) := by
  intro x hx
  -- The zero-outside predicate is exactly the support condition for `Pi.spanSubset`.
  exact (mem_supportSpanSubset_iff (S := S) x).2 <|
    (mem_zero_outside_iff S x).1 hx

/-- Helper for Exercise 7.19: the affine-span direction of any support-restricted set stays inside
the corresponding supported-coordinate subspace. -/
private lemma direction_le_supportSpanSubset_of_subset_zeroOutside
    (S : Finset V) {P : Set (V → ℝ)}
    (hP : P ⊆ zero_outside S) :
    (affineSpan ℝ P).direction ≤ Pi.spanSubset ℝ (↑S : Set V) := by
  let H : AffineSubspace ℝ (V → ℝ) :=
    AffineSubspace.mk' (0 : V → ℝ) (Pi.spanSubset ℝ (↑S : Set V))
  have hP_le_H : P ⊆ H := by
    intro x hx
    change x -ᵥ (0 : V → ℝ) ∈ Pi.spanSubset ℝ (↑S : Set V)
    rw [mem_supportSpanSubset_iff]
    -- Subtracting the base point `0` does not change the support restriction.
    simpa [vsub_eq_sub] using (mem_zero_outside_iff S x).1 (hP hx)
  have h_aff_le : affineSpan ℝ P ≤ H := (affineSpan_le).2 hP_le_H
  -- Passing to directions drops the affine base point and keeps the support subspace.
  simpa [H] using
    (AffineSubspace.direction_le h_aff_le :
      (affineSpan ℝ P).direction ≤ H.direction)

/-- Helper for Exercise 7.19: the support-restricted stable-set polytope spans the full supported
coordinate subspace on `S`. -/
private theorem supportRestrictedStableSetPolytope_finrank
    (S : Finset V) :
    Module.finrank ℝ (affineSpan ℝ (STAB(G) ∩ zero_outside S)).direction = S.card := by
  let P : Set (V → ℝ) := STAB(G) ∩ zero_outside S
  have hzero_mem : (0 : V → ℝ) ∈ P := by
    -- The empty stable set contributes the origin, which is supported on every finite set.
    refine ⟨?_, ?_⟩
    · have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
        stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
      simpa [stableSetIndicatorEmpty] using h0
    · rw [mem_zero_outside_iff]
      intro v hv
      simp
  have h_direction :
      (affineSpan ℝ P).direction = Submodule.span ℝ P := by
    -- Because the origin lies in `P`, its affine directions are exactly the linear span of `P`.
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ hzero_mem]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [P, vsub_eq_sub]
    · intro hx
      refine ⟨x, hx, ?_⟩
      simp [vsub_eq_sub]
  have h_span_le :
      Submodule.span ℝ P ≤ Pi.spanSubset ℝ (↑S : Set V) := by
    -- Every point of the support restriction already lies in the supported-coordinate subspace.
    refine Submodule.span_le.mpr ?_
    intro x hx
    exact zeroOutside_subset_supportSpanSubset (S := S) hx.2
  have h_span_ge :
      Pi.spanSubset ℝ (↑S : Set V) ≤ Submodule.span ℝ P := by
    -- Each supported coordinate basis vector appears as a singleton stable-set indicator.
    rw [Pi.spanSubset]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨v, hvS, rfl⟩
    have hv_mem : Pi.single v (1 : ℝ) ∈ P := by
      refine ⟨?_, ?_⟩
      · have hsingle : stableSetIndicator ({v} : Finset V) ∈ STAB(G) :=
          stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
        simpa [stableSetIndicatorSingleton] using hsingle
      · rw [mem_zero_outside_iff]
        intro u hu
        have huv : u ≠ v := by
          intro huv
          exact hu (huv ▸ hvS)
        simp [Pi.single_apply, huv]
    exact Submodule.subset_span hv_mem
  have h_span :
      Submodule.span ℝ P = Pi.spanSubset ℝ (↑S : Set V) :=
    le_antisymm h_span_le h_span_ge
  -- The support restriction has the same dimension as the supported-coordinate subspace.
  calc
    Module.finrank ℝ (affineSpan ℝ P).direction
        = Module.finrank ℝ (Submodule.span ℝ P) := by
            rw [h_direction]
    _ = Module.finrank ℝ (Pi.spanSubset ℝ (↑S : Set V)) := by
          rw [h_span]
    _ = Set.ncard (↑S : Set V) := by
          rw [Pi.dim_spanSubset]
    _ = S.card := by
          simpa using (Set.ncard_coe_finset S)

/-- Helper for Exercise 7.19: if a linear functional takes value `1` on a vector of `D`, then
`D ∩ ker L` has codimension one inside `D`. -/
private theorem supportSubspace_finrank_inf_ker_add_one_of_eval_one
    (D : Submodule ℝ (V → ℝ)) (L : (V → ℝ) →ₗ[ℝ] ℝ) {w : V → ℝ}
    (hwD : w ∈ D) (hw : L w = 1) :
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
  have hne : L.domRestrict D ≠ 0 := by
    -- Evaluating the restricted functional at the chosen witness prevents it from vanishing.
    intro hzero
    have hvalue := congrArg (fun f : D →ₗ[ℝ] ℝ ↦ f ⟨w, hwD⟩) hzero
    simpa [LinearMap.domRestrict_apply, hw] using hvalue
  have hdim :
      Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 =
        Module.finrank ℝ ↥D := by
    simpa using Module.Dual.finrank_ker_add_one_of_ne_zero (f := L.domRestrict D) hne
  have hmap :
      (LinearMap.ker (L.domRestrict D)).map D.subtype = D ⊓ LinearMap.ker L := by
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype]
  have hfin :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) =
        Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) := by
    -- The subtype embedding identifies the restricted kernel with the ambient kernel cut.
    rw [← hmap]
    simpa using
      (Submodule.finrank_map_subtype_eq (R := ℝ) (p := D)
        (q := LinearMap.ker (L.domRestrict D)))
  calc
    Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1
        = Module.finrank ℝ ↥(LinearMap.ker (L.domRestrict D)) + 1 := by
            rw [hfin]
    _ = Module.finrank ℝ ↥D := hdim

/-- Helper for Exercise 7.19: the supported zero-sum subspace on a nonempty finite support has
dimension `|S| - 1`. -/
private theorem supportRestrictedZeroSum_finrank
    (S : Finset V) (hS : S.Nonempty) :
    Module.finrank ℝ
        ↥(Pi.spanSubset ℝ (↑S : Set V) ⊓
          LinearMap.ker (stableSetDotProductLinearMap (stableSetIndicator S))) =
      S.card - 1 := by
  rcases hS with ⟨v, hvS⟩
  let D : Submodule ℝ (V → ℝ) := Pi.spanSubset ℝ (↑S : Set V)
  let L : (V → ℝ) →ₗ[ℝ] ℝ := stableSetDotProductLinearMap (stableSetIndicator S)
  have hvD : (Pi.single v (1 : ℝ) : V → ℝ) ∈ D := by
    -- The support basis vector at `v` is one of the generators of `Pi.spanSubset`.
    rw [Pi.mem_spanSubset_iff]
    intro u hu
    have huv : u ≠ v := by
      intro huv
      exact hu (huv ▸ hvS)
    simp [Pi.single_apply, huv]
  have hv_eval : L (Pi.single v (1 : ℝ)) = 1 := by
    -- The indicator of `S` evaluates to `1` on the basis vector anchored at a support vertex.
    calc
      L (Pi.single v (1 : ℝ))
          = stableSetIndicator S ⬝ᵥ (Pi.single v (1 : ℝ)) := by
              simp [L, stableSetDotProductLinearMap_apply]
      _ = S.sum (Pi.single v (1 : ℝ)) := by
            rw [stableSetIndicator_dotProduct]
      _ = 1 := by
            simp [hvS]
  have hcodim :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) + 1 = Module.finrank ℝ ↥D := by
    -- Restrict the sum functional to the supported-coordinate subspace and apply the codimension
    -- one kernel theorem inside the supported-coordinate ambient subspace.
    exact supportSubspace_finrank_inf_ker_add_one_of_eval_one D L hvD hv_eval
  have hdim_D : Module.finrank ℝ ↥D = S.card := by
    -- The supported-coordinate subspace has one degree of freedom per support vertex.
    calc
      Module.finrank ℝ ↥D = Module.finrank ℝ (Pi.spanSubset ℝ (↑S : Set V)) := by
        rfl
      _ = Set.ncard (↑S : Set V) := by
            rw [Pi.dim_spanSubset]
      _ = S.card := by
            simpa using (Set.ncard_coe_finset S)
  -- Rearranging the codimension-one equality gives the desired support-size-minus-one formula.
  have hcard_pos : 1 ≤ S.card := by
    exact Finset.card_pos.mpr ⟨v, hvS⟩
  have hdim_inter :
      Module.finrank ℝ ↥(D ⊓ LinearMap.ker L) = S.card - 1 := by
    omega
  simpa [D, L] using hdim_inter

/-- Helper for Exercise 7.19: an equality slice inside the support restriction has direction
contained in the supported zero-sum subspace. -/
private lemma equalitySliceDirection_le_supportZeroSum
    (S : Finset V) (P : Set (V → ℝ)) (δ : ℝ) (x₀ : V → ℝ)
    (hx₀_eq : S.sum x₀ = δ) :
    (affineSpan ℝ {x : V → ℝ | x ∈ P ∩ zero_outside S ∧ S.sum x = δ}).direction ≤
      Pi.spanSubset ℝ (↑S : Set V) ⊓
        LinearMap.ker (stableSetDotProductLinearMap (stableSetIndicator S)) := by
  have hsupport :
      (affineSpan ℝ {x : V → ℝ | x ∈ P ∩ zero_outside S ∧ S.sum x = δ}).direction ≤
        Pi.spanSubset ℝ (↑S : Set V) := by
    -- The face points already satisfy the support restriction, so every difference stays
    -- supported on `S`.
    apply direction_le_supportSpanSubset_of_subset_zeroOutside (S := S)
    intro x hx
    exact hx.1.2
  have hsum :
      (affineSpan ℝ {x : V → ℝ | x ∈ P ∩ zero_outside S ∧ S.sum x = δ}).direction ≤
        LinearMap.ker (stableSetDotProductLinearMap (stableSetIndicator S)) := by
    have hx₀_dot : stableSetIndicator S ⬝ᵥ x₀ = δ := by
      simpa [stableSetIndicator_dotProduct] using hx₀_eq
    have hEq :
        {x : V → ℝ | x ∈ P ∩ zero_outside S ∧ S.sum x = δ} =
          {x : V → ℝ |
            x ∈ P ∩ zero_outside S ∧
              stableSetIndicator S ⬝ᵥ x = δ} := by
      ext x
      simp [stableSetIndicator_dotProduct]
    rw [hEq]
    exact equalitySetDirectionLeKer
      (P := P ∩ zero_outside S) (c := stableSetIndicator S) (x₀ := x₀) (δ := δ) hx₀_dot
  -- Combine the support restriction and the equality-preserving kernel inclusion.
  exact le_inf hsupport hsum

/-- Helper for Exercise 7.19: cyclic coordinate differences generate every supported vector
whose coordinate sum is zero. -/
private lemma supportedZeroSum_le_of_cyclicSteps
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ι ↪ V) (σ : Equiv.Perm ι) (i₀ : ι) (D : Submodule ℝ (V → ℝ))
    (hcycle : σ.IsCycle) (hsupport : σ.support = Finset.univ)
    (hsteps : ∀ i,
      (Pi.single (f i) (1 : ℝ) - Pi.single (f (σ i)) 1 : V → ℝ) ∈ D) :
    Pi.spanSubset ℝ (↑(Finset.univ.map f) : Set V) ⊓
        LinearMap.ker
          (stableSetDotProductLinearMap (stableSetIndicator (Finset.univ.map f))) ≤ D := by
  classical
  have hmove : ∀ i, σ i ≠ i := by
    intro i
    exact Equiv.Perm.mem_support.mp <| by simpa [hsupport]
  have horbit : ∀ n i,
      (Pi.single (f i) (1 : ℝ) - Pi.single (f ((σ ^ n) i)) 1 : V → ℝ) ∈ D := by
    intro n
    induction n with
    | zero =>
        intro i
        simp
    | succ n hn =>
        intro i
        have hfirst := hn i
        have hlast := hsteps ((σ ^ n) i)
        -- The two adjacent orbit differences telescope to the longer orbit difference.
        simpa [pow_succ', sub_eq_add_neg, add_assoc] using D.add_mem hfirst hlast
  have hdiff : ∀ i,
      (Pi.single (f i) (1 : ℝ) - Pi.single (f i₀) 1 : V → ℝ) ∈ D := by
    intro i
    obtain ⟨n, hn⟩ := hcycle.exists_pow_eq (hmove i) (hmove i₀)
    simpa [hn] using horbit n i
  intro x hx
  have hxSupport : x ∈ Pi.spanSubset ℝ (↑(Finset.univ.map f) : Set V) := hx.1
  have hxSum : ∑ i : ι, x (f i) = 0 := by
    have hker := LinearMap.mem_ker.mp hx.2
    rw [stableSetDotProductLinearMap_apply, stableSetIndicator_dotProduct] at hker
    simpa using hker
  have hxExpand :
      x = ∑ i : ι, x (f i) •
        (Pi.single (f i) (1 : ℝ) - Pi.single (f i₀) 1 : V → ℝ) := by
    funext v
    by_cases hv : v ∈ Finset.univ.map f
    · rw [Finset.mem_map] at hv
      obtain ⟨i, -, rfl⟩ := hv
      by_cases hi₀ : i = i₀
      · subst i
        simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_apply,
          f.injective.eq_iff, smul_eq_mul]
        calc
          x (f i₀) = x (f i₀) - ∑ j, x (f j) := by rw [hxSum, sub_zero]
          _ = ∑ j, x (f j) * ((if i₀ = j then 1 else 0) - 1) := by
            simp [mul_sub, Finset.sum_sub_distrib]
      · simp [Pi.single_apply, f.injective.eq_iff, hi₀]
    · have hxv : x v = 0 :=
        (mem_supportSpanSubset_iff (S := Finset.univ.map f) x).1 hxSupport v hv
      have hne : ∀ i, f i ≠ v := by
        intro i hi
        apply hv
        exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, hi⟩
      simp [hxv, Pi.single_apply, hne]
  rw [hxExpand]
  exact Submodule.sum_mem D fun i _ ↦ D.smul_mem (x (f i)) (hdiff i)

/-- Helper for Exercise 7.19: a nonempty valid supported equality slice is a facet once its
directions contain the full supported zero-sum subspace. -/
private theorem supportedStableSetEquality_isFacetOf
    (S : Finset V) (δ : ℝ) (hS : S.Nonempty)
    (hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → S.sum x ≤ δ)
    (hfaceNonempty :
      {x : V → ℝ | x ∈ STAB(G) ∩ zero_outside S ∧ S.sum x = δ}.Nonempty)
    (hlower :
      Pi.spanSubset ℝ (↑S : Set V) ⊓
          LinearMap.ker (stableSetDotProductLinearMap (stableSetIndicator S)) ≤
        (affineSpan ℝ
          {x : V → ℝ | x ∈ STAB(G) ∩ zero_outside S ∧ S.sum x = δ}).direction) :
    IsFacetOf (STAB(G) ∩ zero_outside S)
      {x : V → ℝ | x ∈ STAB(G) ∩ zero_outside S ∧ S.sum x = δ} := by
  classical
  let F : Set (V → ℝ) :=
    {x : V → ℝ | x ∈ STAB(G) ∩ zero_outside S ∧ S.sum x = δ}
  obtain ⟨x₀, hx₀⟩ := hfaceNonempty
  have hx₀Dot : stableSetIndicator S ⬝ᵥ x₀ = δ := by
    simpa [stableSetIndicator_dotProduct] using hx₀.2
  have hvalidSupported :
      ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) ∩ zero_outside S →
        stableSetIndicator S ⬝ᵥ x ≤ δ := by
    intro x hx
    simpa [stableSetIndicator_dotProduct] using hvalid hx.1
  have hExposed : IsExposed ℝ (STAB(G) ∩ zero_outside S) F := by
    -- Validity and the chosen tight point expose precisely the equality slice.
    simpa [F, stableSetIndicator_dotProduct] using
      equalitySetIsExposed hvalidSupported hx₀.1 hx₀Dot
  have hupper :
      (affineSpan ℝ F).direction ≤
        Pi.spanSubset ℝ (↑S : Set V) ⊓
          LinearMap.ker (stableSetDotProductLinearMap (stableSetIndicator S)) := by
    simpa [F] using
      equalitySliceDirection_le_supportZeroSum S (STAB(G)) δ x₀ hx₀.2
  have hDirection :
      (affineSpan ℝ F).direction =
        Pi.spanSubset ℝ (↑S : Set V) ⊓
          LinearMap.ker (stableSetDotProductLinearMap (stableSetIndicator S)) := by
    exact le_antisymm hupper (by simpa [F] using hlower)
  rw [isFacetOf_iff]
  refine ⟨⟨x₀, hx₀⟩, hExposed, ?_⟩
  -- The direction equality reduces the facet equation to the two established support dimensions.
  calc
    Module.finrank ℝ (affineSpan ℝ F).direction + 1 = (S.card - 1) + 1 := by
      rw [hDirection, supportRestrictedZeroSum_finrank S hS]
    _ = S.card := Nat.sub_add_cancel (Finset.one_le_card.mpr hS)
    _ = Module.finrank ℝ (affineSpan ℝ (STAB(G) ∩ zero_outside S)).direction := by
      rw [supportRestrictedStableSetPolytope_finrank]

end SupportedFacetHelpers

section CyclicCountingHelpers

variable [Fintype V]

/-- Helper for Exercise 7.19: the successor index in the cyclic order on `C.length`. -/
private def cycleNextIndex (C : CycleSupport V) (i : Fin C.length) : Fin C.length :=
  finRotate C.length i

/-- Helper for Exercise 7.19: the predecessor index in the cyclic order on `C.length`. -/
private def cyclePrevIndex (C : CycleSupport V) (i : Fin C.length) : Fin C.length :=
  (finRotate C.length).symm i

/-- Helper for Exercise 7.19: the predecessor index maps back to `i` under one cyclic successor
step. -/
private lemma cycleNextIndex_prev (C : CycleSupport V) (i : Fin C.length) :
    cycleNextIndex C (cyclePrevIndex C i) = i := by
  -- Route correction: the cyclic predecessor/successor API is now normalized through
  -- `finRotate`, so the inverse law is a direct permutation identity.
  simpa [cycleNextIndex, cyclePrevIndex] using
    Equiv.apply_symm_apply (finRotate C.length) i

/-- Helper for Exercise 7.19: applying the predecessor to the cyclic successor returns the original
index. -/
private lemma cyclePrevIndex_next (C : CycleSupport V) (i : Fin C.length) :
    cyclePrevIndex C (cycleNextIndex C i) = i := by
  -- The inverse permutation identity gives the successor-then-predecessor cancellation.
  simpa [cycleNextIndex, cyclePrevIndex] using
    Equiv.symm_apply_apply (finRotate C.length) i

/-- Helper for Exercise 7.19: the predecessor of a cycle index is never the index itself. -/
private lemma cyclePrevIndex_ne (C : CycleSupport V) (i : Fin C.length) :
    cyclePrevIndex C i ≠ i := by
  -- `finRotate` moves every point when the cycle has length at least `2`, so its inverse cannot
  -- fix `i` either.
  have hmove : finRotate C.length i ≠ i := by
    have hsupport : i ∈ (finRotate C.length).support := by
      simpa [support_finRotate_of_le (le_trans (by decide : 2 ≤ 3) C.length_ge_three)]
    exact Equiv.Perm.mem_support.mp hsupport
  intro hprev
  have hfixed : finRotate C.length i = i := by
    have hnext := cycleNextIndex_prev C i
    rw [hprev] at hnext
    simpa [cycleNextIndex] using hnext
  exact hmove hfixed

/-- Helper for Exercise 7.19: the `i`-th cycle edge is the unordered pair of consecutive labelled
vertices. -/
private def cycleEdge (C : CycleSupport V) (i : Fin C.length) : Sym2 V :=
  s(C.verts i, C.verts (cycleNextIndex C i))

/-- Helper for Exercise 7.19: the indexed odd-cycle edge multipliers assign weight `1 / 2` to each
cycle edge occurrence. -/
private noncomputable def oddCycleEdgeMultiplier
    (C : CycleSupport V) : Sym2 V → ℝ :=
  fun e ↦ ∑ i : Fin C.length, if e = cycleEdge C i then (1 / 2 : ℝ) else 0

/-- Helper for Exercise 7.19: every indexed cycle edge is an actual edge of `G` when `C` is
contained in `G`. -/
private lemma cycleEdge_mem_edgeSet
    (C : CycleSupport V) (hC : C.IsContainedIn G) (i : Fin C.length) :
    cycleEdge C i ∈ G.edgeSet := by
  -- The containment hypothesis is exactly the adjacency statement for consecutive cycle
  -- vertices, and `finRotate` agrees with the original modulo-successor index.
  have hnext :
      cycleNextIndex C i =
        ⟨(i.1 + 1) % C.length,
          Nat.mod_lt _ (Nat.lt_of_lt_of_le (by decide) C.length_ge_three)⟩ := by
    simpa [cycleNextIndex, Fin.add_def] using (finRotate_apply (n := C.length) i)
  rw [cycleEdge, SimpleGraph.mem_edgeSet, hnext]
  exact hC i

/-- Helper for Exercise 7.19: the odd-cycle edge multipliers are coordinatewise nonnegative. -/
private lemma oddCycleEdgeMultiplier_nonneg
    (C : CycleSupport V) :
    ∀ e : Sym2 V, 0 ≤ oddCycleEdgeMultiplier C e := by
  intro e
  -- Each summand is either `0` or `1 / 2`.
  refine Finset.sum_nonneg ?_
  intro i hi
  by_cases h : e = cycleEdge C i
  · simp [oddCycleEdgeMultiplier, h]
  · simp [oddCycleEdgeMultiplier, h]

/-- Helper for Exercise 7.19: a nonzero odd-cycle edge multiplier can only occur on an actual edge
of `G`. -/
private lemma oddCycleEdgeMultiplier_support
    (C : CycleSupport V)
    (hC : C.IsContainedIn G) :
    ∀ e : Sym2 V, oddCycleEdgeMultiplier C e ≠ 0 → e ∈ G.edgeSet := by
  intro e he
  by_contra hedgenot
  have hnoMatch : ∀ i : Fin C.length, e ≠ cycleEdge C i := by
    intro i hi
    apply hedgenot
    rw [hi]
    exact cycleEdge_mem_edgeSet (G := G) C hC i
  have hzero : oddCycleEdgeMultiplier C e = 0 := by
    simp [oddCycleEdgeMultiplier, hnoMatch]
  exact he hzero

/-- Helper for Exercise 7.19: the sum of the odd-cycle edge multipliers is `|C| / 2`. -/
private lemma oddCycleEdgeMultiplier_sum
    (C : CycleSupport V) :
    ∑ e : Sym2 V, oddCycleEdgeMultiplier C e = (C.length : ℝ) / 2 := by
  -- Reindex the global `Sym2 V` sum by the cycle index family and collapse each inner singleton.
  calc
    ∑ e : Sym2 V, oddCycleEdgeMultiplier C e
        = ∑ e : Sym2 V, ∑ i : Fin C.length,
            if e = cycleEdge C i then (1 / 2 : ℝ) else 0 := by
              rfl
    _ = ∑ i : Fin C.length, ∑ e : Sym2 V,
            if e = cycleEdge C i then (1 / 2 : ℝ) else 0 := by
              rw [Finset.sum_comm]
    _ = ∑ i : Fin C.length, (1 / 2 : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp
    _ = (C.length : ℝ) / 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [div_eq_mul_inv]

/-- Helper for Exercise 7.19: a cycle vertex belongs to exactly the two incident indexed cycle
edges, written in the successor-facing `finRotate` normal form. -/
private lemma mem_cycleEdge_iff
    (C : CycleSupport V) (i j : Fin C.length) :
    C.verts j ∈ cycleEdge C i ↔ i = j ∨ cycleNextIndex C i = j := by
  -- Route correction: classify the incident cycle edges through the rotate successor instead of
  -- reopening raw `%` arithmetic on indices.
  rw [cycleEdge, Sym2.mem_iff]
  constructor
  · intro hmem
    rcases hmem with hmem | hmem
    · exact Or.inl (C.verts.injective hmem).symm
    · exact Or.inr (C.verts.injective hmem).symm
  · intro hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · exact Or.inr (by rw [hmem])

/-- Helper for Exercise 7.19: vertices outside the cycle support lie on no indexed cycle edge. -/
private lemma not_mem_cycleEdge_of_not_vertex
    (C : CycleSupport V) {v : V}
    (hv : v ∉ C.vertexFinset) (i : Fin C.length) :
    v ∉ cycleEdge C i := by
  -- Each cycle edge endpoint is one of the labelled vertices of `C`.
  intro hmem
  rw [cycleEdge, Sym2.mem_iff] at hmem
  rcases hmem with hmem | hmem
  · exact hv <| (CycleSupport.mem_vertexFinset_iff C).2 ⟨i, hmem.symm⟩
  · exact hv <| (CycleSupport.mem_vertexFinset_iff C).2 ⟨cycleNextIndex C i, hmem.symm⟩

/-- Helper for Exercise 7.19: the odd-cycle edge multipliers aggregate to the indicator of
`C.vertexFinset`. -/
private lemma oddCycleEdgeMultiplier_coefficients
    (C : CycleSupport V) :
    (fun v ↦ ∑ e : Sym2 V, (if v ∈ e then oddCycleEdgeMultiplier C e else 0)) =
      stableSetIndicator C.vertexFinset := by
  classical
  funext v
  by_cases hv : v ∈ C.vertexFinset
  · rcases (CycleSupport.mem_vertexFinset_iff C).1 hv with ⟨j, rfl⟩
    have hincident :
        ∀ i : Fin C.length,
          C.verts j ∈ cycleEdge C i ↔ i = j ∨ i = cyclePrevIndex C j := by
      intro i
      rw [mem_cycleEdge_iff]
      constructor
      · intro hmem
        rcases hmem with rfl | hmem
        · exact Or.inl rfl
        · exact Or.inr <| by
            calc
              i = cyclePrevIndex C (cycleNextIndex C i) := by
                rw [cyclePrevIndex_next]
              _ = cyclePrevIndex C j := by rw [hmem]
      · intro hmem
        rcases hmem with rfl | hmem
        · exact Or.inl rfl
        · exact Or.inr <| by
            calc
              cycleNextIndex C i = cycleNextIndex C (cyclePrevIndex C j) := by rw [hmem]
              _ = j := cycleNextIndex_prev C j
    have htwo :
        (∑ i : Fin C.length, if C.verts j ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) = 1 := by
      have hfilter :
          (Finset.univ.filter fun i : Fin C.length ↦ C.verts j ∈ cycleEdge C i) =
            {j, cyclePrevIndex C j} := by
        ext i
        simp [hincident i]
      rw [← Finset.sum_filter, hfilter]
      have hcard : ({j, cyclePrevIndex C j} : Finset (Fin C.length)).card = 2 :=
        Finset.card_pair (cyclePrevIndex_ne C j).symm
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      norm_num
    -- Swapping the edge/index sums reduces the coefficient at `C.verts j` to its two
    -- incident `1 / 2` contributions.
    calc
      ∑ e : Sym2 V, (if C.verts j ∈ e then oddCycleEdgeMultiplier C e else 0)
          = ∑ e : Sym2 V, (if C.verts j ∈ e then
              ∑ i : Fin C.length, if e = cycleEdge C i then (1 / 2 : ℝ) else 0
            else 0) := by
              rfl
      _ = ∑ e : Sym2 V, ∑ i : Fin C.length,
            (if C.verts j ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              by_cases hmem : C.verts j ∈ e
              · simp [hmem]
              · simp [hmem]
      _ = ∑ i : Fin C.length, ∑ e : Sym2 V,
            (if C.verts j ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin C.length, (if C.verts j ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hmem : C.verts j ∈ cycleEdge C i
            · rw [Finset.sum_eq_single (cycleEdge C i)]
              · simp [hmem]
              · intro x hx hxeq
                simp [hxeq]
              · simp
            · have hsum :
                (∑ x, if C.verts j ∈ x then if x = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) =
                  0 := by
                refine Finset.sum_eq_zero ?_
                intro x hx
                by_cases hxeq : x = cycleEdge C i
                · simp [hxeq, hmem]
                · simp [hxeq]
              simpa [hmem] using hsum
      _ = 1 := htwo
      _ = stableSetIndicator C.vertexFinset (C.verts j) := by
            simp [stableSetIndicator, CycleSupport.mem_vertexFinset_iff]
  · have hzero :
      (∑ i : Fin C.length, if v ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [not_mem_cycleEdge_of_not_vertex (C := C) hv i]
    -- Outside the cycle support every incidence term vanishes, so the aggregated coefficient is
    -- the zero coordinate of the support indicator.
    calc
      ∑ e : Sym2 V, (if v ∈ e then oddCycleEdgeMultiplier C e else 0)
          = ∑ e : Sym2 V, (if v ∈ e then
              ∑ i : Fin C.length, if e = cycleEdge C i then (1 / 2 : ℝ) else 0
            else 0) := by
              rfl
      _ = ∑ e : Sym2 V, ∑ i : Fin C.length,
            (if v ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro e he
              by_cases hmem : v ∈ e
              · simp [hmem]
              · simp [hmem]
      _ = ∑ i : Fin C.length, ∑ e : Sym2 V,
            (if v ∈ e then if e = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin C.length, (if v ∈ cycleEdge C i then (1 / 2 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hmem : v ∈ cycleEdge C i
            · rw [Finset.sum_eq_single (cycleEdge C i)]
              · simp [hmem]
              · intro x hx hxeq
                simp [hxeq]
              · simp
            · have hsum :
                (∑ x, if v ∈ x then if x = cycleEdge C i then (1 / 2 : ℝ) else 0 else 0) = 0 := by
                refine Finset.sum_eq_zero ?_
                intro x hx
                by_cases hxeq : x = cycleEdge C i
                · simp [hxeq, hmem]
                · simp [hxeq]
              simpa [hmem] using hsum
      _ = 0 := hzero
      _ = stableSetIndicator C.vertexFinset v := by
            simp [stableSetIndicator, hv]

/-- Helper for Exercise 7.19: the floored total odd-cycle multiplier equals the odd-cycle
right-hand side. -/
private lemma oddCycleEdgeMultiplier_floor
    (C : CycleSupport V)
    (hodd : Odd C.length) :
    ((Int.floor (∑ e : Sym2 V, oddCycleEdgeMultiplier C e) : ℤ) : ℝ) =
      odd_cycle_inequality_rhs C := by
  rcases hodd.exists_bit1 with ⟨m, hm⟩
  -- Rewrite the odd length as `2 * m + 1`, then evaluate the floor of `m + 1/2`.
  rw [oddCycleEdgeMultiplier_sum, odd_cycle_inequality_rhs_eq, hm]
  have hhalf : ((((2 * m + 1 : ℕ) : ℝ) / 2)) = (m : ℝ) + (1 / 2 : ℝ) := by
    field_simp
    norm_num
  rw [hhalf, Int.floor_natCast_add]
  norm_num

end CyclicCountingHelpers

section ChvatalCountingHelpers

variable [Fintype V]

/-- Helper for Exercise 7.19: the cyclic offset from `i` to `j` is the value of the modular
`Fin` difference `j - i`. -/
private lemma cyclic_offset_eq_sub_val {m : ℕ} [NeZero m] (i j : Fin m) :
    cyclic_offset i j = (j - i).1 := by
  -- Split on the linear order of `i` and `j`, then reduce to the two standard modular forms.
  rw [cyclic_offset_eq]
  by_cases hij : i ≤ j
  · rw [show j.1 + m - i.1 = (j.1 - i.1) + m by omega, Nat.add_mod_right,
      Fin.sub_val_of_le hij]
    exact Nat.mod_eq_of_lt (by omega)
  · have hij' : j < i := lt_of_not_ge hij
    have hsub : (j - i).1 = m + j.1 - i.1 := by
      exact (Fin.coe_sub_iff_lt (a := j) (b := i)).2 hij'
    have hmod_lt : j.1 + m - i.1 < m := by
      omega
    rw [Nat.mod_eq_of_lt hmod_lt]
    calc
      j.1 + m - i.1 = m + j.1 - i.1 := by omega
      _ = (j - i).1 := hsub.symm

/-- Helper for Exercise 7.19: exactly `W.width + 1` cyclic start indices place the labelled
vertex `j` inside a forward web block. -/
private lemma webForwardBlockStartCount
    (W : WebSupport V) (j : Fin W.length) :
    Fintype.card {i : Fin W.length // cyclic_offset i j ≤ W.width} = W.width + 1 := by
  classical
  have hlen_pos : 0 < W.length := by
    exact Nat.succ_le_iff.mp (le_trans (by omega : 1 ≤ 2 * W.width + 1) W.width_bound)
  letI : NeZero W.length := ⟨Nat.ne_of_gt hlen_pos⟩
  have hwidth_le : W.width + 1 ≤ W.length := by
    exact le_trans (by omega : W.width + 1 ≤ 2 * W.width + 1) W.width_bound
  let f : Fin (W.width + 1) → {i : Fin W.length // cyclic_offset i j ≤ W.width} :=
    fun a ↦
      let a' : Fin W.length := a.castLT (lt_of_lt_of_le a.2 hwidth_le)
      ⟨j - a', by
        -- The translated start `j - a` has cyclic offset exactly `a`.
        rw [cyclic_offset_eq_sub_val]
        have hcancel : j - (j - a') = a' := by
          abel
        rw [hcancel]
        exact Nat.le_of_lt_succ a.2⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval : (f a).1 = (f b).1 := congrArg Subtype.val hab
      have hcast : (a.castLT (lt_of_lt_of_le a.2 hwidth_le) : Fin W.length) =
          b.castLT (lt_of_lt_of_le b.2 hwidth_le) := by
        have h := congrArg (fun t : Fin W.length ↦ j - t) hval
        simpa [f] using h
      apply Fin.ext
      exact congrArg (fun t : Fin W.length ↦ t.1) hcast
    · intro i
      let a : Fin (W.width + 1) := ⟨cyclic_offset i.1 j, Nat.lt_succ_of_le i.2⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      have haeq :
          (a.castLT (lt_of_lt_of_le a.2 hwidth_le) : Fin W.length) = j - i.1 := by
        apply Fin.ext
        change cyclic_offset i.1 j = (j - i.1).1
        exact cyclic_offset_eq_sub_val i.1 j
      have h := congrArg (fun t : Fin W.length ↦ j - t) haeq
      simpa [a, f] using h
  simpa using (Fintype.card_congr (Equiv.ofBijective f hf_bij)).symm

/-- Helper for Exercise 7.19: summing the constant web multiplier `1 / (k + 1)` over the `n`
labelled web blocks has floored total `⌊n / (k + 1)⌋`. -/
private lemma webBlockMultiplier_floor
    (W : WebSupport V) :
    ((Int.floor (∑ _i : Fin W.length, (1 / (W.width + 1 : ℝ))) : ℤ) : ℝ) =
      web_inequality_rhs W := by
  -- Normalize the constant sum to the real division `W.length / (W.width + 1)`.
  have hsum :
      ∑ _i : Fin W.length, (1 / (W.width + 1 : ℝ)) =
        (W.length : ℝ) / (W.width + 1) := by
    simp [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [hsum, web_inequality_rhs_eq]
  have hfloor :
      Int.floor ((W.length : ℝ) / (W.width + 1 : ℝ)) =
        (W.length / (W.width + 1) : ℤ) := by
    calc
      Int.floor ((W.length : ℝ) / (W.width + 1 : ℝ))
          = Int.floor (W.length : ℝ) / (W.width + 1) := by
              simpa using (Int.floor_div_natCast (a := (W.length : ℝ)) (n := W.width + 1))
      _ = (W.length / (W.width + 1) : ℤ) := by
            rw [Int.floor_natCast]
  have hcast :
      (((W.length / (W.width + 1) : ℤ) : ℝ)) =
        ((W.length / (W.width + 1) : ℕ) : ℝ) := by
    have hdiv := (Int.natCast_div W.length (W.width + 1)).symm
    exact congrArg (fun z : ℤ ↦ (z : ℝ)) hdiv
  rw [hfloor]
  exact hcast

/-- Helper for Exercise 7.19: for an odd antihole support, summing the constant multiplier
`2 / (|H| - 1)` over the `|H|` cyclic clique candidates has floored total `2`. -/
private lemma antiholeCliqueMultiplier_floor
    (H : AntiholeSupport V)
    (hodd : Odd H.length) :
    ((Int.floor (∑ _i : Fin H.length, (2 / (H.length - 1 : ℝ))) : ℤ) : ℝ) = 2 := by
  rcases hodd.exists_bit1 with ⟨m, hm⟩
  have hlen_lower : 5 ≤ 2 * m + 1 := by
    simpa [hm] using H.length_ge_five
  have hm_two : 2 ≤ m := by
    omega
  have hm_pos : 0 < m := by
    exact lt_of_lt_of_le (by norm_num) hm_two
  have hm_real_pos : (0 : ℝ) < m := by
    exact_mod_cast hm_pos
  have hm_ne : (m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm_pos
  have hsum :
      ∑ _i : Fin H.length, (2 / (H.length - 1 : ℝ)) = (2 : ℝ) + 1 / m := by
    rw [hm]
    simp [Finset.sum_const, nsmul_eq_mul]
    field_simp [hm_ne]
  have hfrac_nonneg : 0 ≤ (1 : ℝ) / m := by
    positivity
  have hfrac_lt : (1 : ℝ) / m < 1 := by
    have hm_one_lt : (1 : ℝ) < m := by
      exact_mod_cast hm_two
    rw [div_lt_iff₀ hm_real_pos]
    nlinarith
  have hfrac_floor : Int.floor ((1 : ℝ) / m) = 0 := by
    exact (Int.floor_eq_zero_iff).2 ⟨hfrac_nonneg, hfrac_lt⟩
  have hfloor : Int.floor ((2 : ℝ) + 1 / m) = 2 := by
    rw [show ((2 : ℝ) + 1 / m) = ((2 : ℕ) : ℝ) + 1 / m by norm_num,
      Int.floor_natCast_add, hfrac_floor]
    norm_num
  rw [hsum, hfloor]
  norm_num

end ChvatalCountingHelpers

section FacetCombinatorialHelpers

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Helper for Exercise 7.19: a zero cyclic offset identifies its two endpoints. -/
private lemma cyclicOffset_eq_zero_iff {m : ℕ} [NeZero m] (i j : Fin m) :
    cyclic_offset i j = 0 ↔ i = j := by
  -- Modular subtraction is zero exactly when the two residues agree.
  rw [cyclic_offset_eq_sub_val]
  constructor
  · intro h
    have hsub : j - i = 0 := Fin.ext h
    exact (sub_eq_zero.mp hsub).symm
  · rintro rfl
    simp

/-- Helper for Exercise 7.19: cyclic offset one is the successor relation generated by
`finRotate`. -/
private lemma cyclicOffset_eq_one_iff {m : ℕ} [NeZero m] (hm : 2 ≤ m) (i j : Fin m) :
    cyclic_offset i j = 1 ↔ j = finRotate m i := by
  -- Translate the numerical offset to an equality in the additive group `Fin m`.
  rw [cyclic_offset_eq_sub_val]
  constructor
  · intro h
    have hone : (j - i : Fin m) = 1 := by
      apply Fin.ext
      simpa [Fin.val_one', Nat.mod_eq_of_lt hm] using h
    have hadd := congrArg (fun z : Fin m ↦ z + i) hone
    simpa [finRotate_apply, add_comm] using hadd
  · rintro rfl
    rw [finRotate_apply, add_comm, add_sub_cancel_right]
    simp [Fin.val_one', Nat.mod_eq_of_lt hm]

/-- Helper for Exercise 7.19: the two directed offsets between distinct cyclic indices sum to
the full cycle length. -/
private lemma cyclicOffset_add_reverse {m : ℕ} [NeZero m]
    (i j : Fin m) (hij : i ≠ j) :
    cyclic_offset i j + cyclic_offset j i = m := by
  -- The two nonzero residues add to a positive multiple of `m` smaller than `2 * m`.
  rw [cyclic_offset_eq_sub_val, cyclic_offset_eq_sub_val]
  have hsumFin : (j - i) + (i - j) = 0 := by abel
  have hmod : ((j - i).1 + (i - j).1) % m = 0 := by
    have hval := congrArg Fin.val hsumFin
    change ((j - i).1 + (i - j).1) % m = 0 at hval
    exact hval
  have hleftPos : 0 < (j - i).1 := by
    have hne : j - i ≠ 0 := sub_ne_zero.mpr hij.symm
    exact Nat.pos_of_ne_zero (fun hzero ↦ hne (Fin.ext hzero))
  have hrightPos : 0 < (i - j).1 := by
    have hne : i - j ≠ 0 := sub_ne_zero.mpr hij
    exact Nat.pos_of_ne_zero (fun hzero ↦ hne (Fin.ext hzero))
  have hdvd : m ∣ (j - i).1 + (i - j).1 := Nat.dvd_of_mod_eq_zero hmod
  rcases hdvd with ⟨t, ht⟩
  have hleftLt := (j - i).2
  have hrightLt := (i - j).2
  have hmPos : 0 < m := NeZero.pos m
  have htPos : 0 < t := by
    by_contra htZero
    have htEq : t = 0 := Nat.eq_zero_of_not_pos htZero
    rw [htEq, mul_zero] at ht
    omega
  have htLt : t < 2 := by
    apply (Nat.mul_lt_mul_left hmPos).mp
    rw [← ht]
    omega
  have htEq : t = 1 := by omega
  rw [htEq, mul_one] at ht
  exact ht

/-- Helper for Exercise 7.19: two successive cyclic rotations are at cyclic distance at least
two in both directions when the cycle has at least five vertices. -/
private lemma cyclicOffset_secondSuccessor_ge_two
    {m : ℕ} [NeZero m] (hm : 5 ≤ m) (i : Fin m) :
    2 ≤ cyclic_offset ((finRotate m) ((finRotate m) i)) i ∧
      2 ≤ cyclic_offset i ((finRotate m) ((finRotate m) i)) := by
  let σ : Equiv.Perm (Fin m) := finRotate m
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le (le_trans (by decide : 2 ≤ 5) hm)
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le (le_trans (by decide : 2 ≤ 5) hm)
  have hmove : σ i ≠ i := by
    exact Equiv.Perm.mem_support.mp <| by simp [hsupport]
  have horder : orderOf σ = m := by
    rw [hcycle.orderOf, hsupport, Finset.card_univ, Fintype.card_fin]
  have hpowNe : ∀ k, 0 < k → k < m → (σ ^ k) i ≠ i := by
    intro k hkPos hkLt hkEq
    have hpow : σ ^ k = 1 := (hcycle.pow_eq_one_iff' hmove).2 hkEq
    have hdvd : orderOf σ ∣ k := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rw [horder] at hdvd
    exact (Nat.not_dvd_of_pos_of_lt hkPos hkLt) hdvd
  have hsecondNe : σ (σ i) ≠ i := by
    simpa [pow_two, Equiv.Perm.mul_apply] using hpowNe 2 (by decide) (by omega)
  have hthirdNe : σ (σ (σ i)) ≠ i := by
    simpa [pow_succ', Equiv.Perm.mul_apply] using hpowNe 3 (by decide) (by omega)
  have hforwardZero : cyclic_offset i (σ (σ i)) ≠ 0 := by
    intro hzero
    exact hsecondNe ((cyclicOffset_eq_zero_iff i (σ (σ i))).1 hzero |>.symm)
  have hforwardOne : cyclic_offset i (σ (σ i)) ≠ 1 := by
    intro hone
    have hEq := (cyclicOffset_eq_one_iff (le_trans (by decide : 2 ≤ 5) hm)
      i (σ (σ i))).1 hone
    exact hmove (σ.injective hEq)
  have hbackwardZero : cyclic_offset (σ (σ i)) i ≠ 0 := by
    intro hzero
    exact hsecondNe ((cyclicOffset_eq_zero_iff (σ (σ i)) i).1 hzero)
  have hbackwardOne : cyclic_offset (σ (σ i)) i ≠ 1 := by
    intro hone
    have hEq := (cyclicOffset_eq_one_iff (le_trans (by decide : 2 ≤ 5) hm)
      (σ (σ i)) i).1 hone
    exact hthirdNe hEq.symm
  -- Excluding offsets zero and one leaves the required lower bounds.
  dsimp [σ] at hforwardZero hforwardOne hbackwardZero hbackwardOne ⊢
  omega

/-- Helper for Exercise 7.19: summing an indicator over an injectively labelled support counts
the selected labels. -/
private lemma cyclicSupport_sum_indicator_eq_card
    (C : CyclicSupport V) (s : Finset V) :
    C.vertexFinset.sum (stableSetIndicator s) =
      ((Finset.univ.filter fun i : Fin C.length ↦ C.verts i ∈ s).card : ℝ) := by
  -- Reindex the support sum along its injective cyclic labelling.
  rw [CyclicSupport.vertexFinset, Finset.sum_map]
  simp [stableSetIndicator]

/-- Helper for Exercise 7.19: an indicator summed over any containing support has value equal to
the cardinality of its own finite support. -/
private lemma support_sum_indicator_eq_card
    {S s : Finset V} (hsub : s ⊆ S) :
    S.sum (stableSetIndicator s) = (s.card : ℝ) := by
  -- Only the coordinates of `s` contribute to the larger support sum.
  simp [stableSetIndicator, Finset.sum_ite_mem]
  rw [Finset.inter_eq_right.mpr hsub]

/-- Helper for Exercise 7.19: powers of `finRotate` advance the underlying residue by their
natural-number exponent. -/
private lemma finRotate_pow_apply_val {m : ℕ} [NeZero m]
    (i : Fin m) (k : ℕ) :
    (((finRotate m) ^ k) i).1 = (i.1 + k) % m := by
  induction k with
  | zero => simpa [Nat.mod_eq_of_lt i.2]
  | succ k hk =>
      -- One more permutation power is one more addition in the cyclic index group.
      rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.add_def, hk]
      calc
        (((i.1 + k) % m + 1 % m) % m) = ((i.1 + k) + 1) % m :=
          (Nat.add_mod (i.1 + k) 1 m).symm
        _ = (i.1 + (k + 1)) % m := by rw [Nat.add_assoc]

/-- Helper for Exercise 7.19: the forward cyclic offset is the exponent carrying its first
endpoint to its second endpoint. -/
private lemma finRotate_pow_cyclicOffset {m : ℕ} [NeZero m]
    (i j : Fin m) :
    ((finRotate m) ^ cyclic_offset i j) i = j := by
  -- Modular subtraction followed by addition recovers the endpoint residue.
  apply Fin.ext
  rw [finRotate_pow_apply_val, cyclic_offset_eq_sub_val]
  change (i + (j - i)).1 = j.1
  have hrecover : i + (j - i) = j := by abel
  exact congrArg Fin.val hrecover

/-- Helper for Exercise 7.19: two powers below the length of a full cyclic rotation agree at one
index only when their exponents agree. -/
private lemma finRotate_pow_apply_injective_below_length
    (C : CycleSupport V) (i : Fin C.length) {a b : ℕ}
    (ha : a < C.length) (hb : b < C.length)
    (happly : ((finRotate C.length) ^ a) i = ((finRotate C.length) ^ b) i) :
    a = b := by
  let σ : Equiv.Perm (Fin C.length) := finRotate C.length
  have htwoThree : 2 ≤ 3 := by decide
  have htwo : 2 ≤ C.length := le_trans htwoThree C.length_ge_three
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le htwo
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le htwo
  have hmove : σ i ≠ i := by
    have hiSupport : i ∈ σ.support := by simp [hsupport]
    exact Equiv.Perm.mem_support.mp hiSupport
  have horder : orderOf σ = C.length := by
    rw [hcycle.orderOf, hsupport, Finset.card_univ, Fintype.card_fin]
  have hpows : σ ^ a = σ ^ b := by
    have happly' : (σ ^ a) i = (σ ^ b) i := by simpa [σ] using happly
    exact hcycle.pow_eq_pow_iff.mpr ⟨i, hmove, happly'⟩
  have hmod : a ≡ b [MOD C.length] := by
    rw [← horder]
    exact pow_eq_pow_iff_modEq.mp hpows
  exact hmod.eq_of_lt_of_lt ha hb

/-- Helper for Exercise 7.19: a bounded interval of powers in the full cyclic orbit is
injectively labelled by its exponent. -/
private lemma cycleIntervalVerts_injective
    (C : CycleSupport V) (i : Fin C.length) (a m : ℕ)
    (hbound : a + m ≤ C.length) :
    Function.Injective
      (fun k : Fin m ↦ C.verts (((finRotate C.length) ^ (a + k.1)) i)) := by
  -- Equality of labelled vertices reduces to equality of two exponents below the cycle length.
  intro k l hkl
  have hklt : a + k.1 < C.length := by omega
  have hllt : a + l.1 < C.length := by omega
  have hpowers := finRotate_pow_apply_injective_below_length C i
    (a := a + k.1) (b := a + l.1) hklt hllt
    (C.verts.injective hkl)
  apply Fin.ext
  omega

/-- Helper for Exercise 7.19: the labelled vertices in a bounded cyclic interval, packaged as
an embedding. -/
private def cycleIntervalVerts
    (C : CycleSupport V) (i : Fin C.length) (a m : ℕ)
    (hbound : a + m ≤ C.length) : Fin m ↪ V :=
  ⟨fun k ↦ C.verts (((finRotate C.length) ^ (a + k.1)) i),
    cycleIntervalVerts_injective C i a m hbound⟩

/-- Helper for Exercise 7.19: the vertices in a cyclic interval form a finite cyclic support.
-/
private def cycleIntervalSupport
    (C : CycleSupport V) (i : Fin C.length) (a m : ℕ)
    (hbound : a + m ≤ C.length) : CyclicSupport V where
  length := m
  verts := cycleIntervalVerts C i a m hbound

/-- Helper for Exercise 7.19: the zero-based chord interval satisfies the bound required by its
cyclic-interval embedding. -/
private lemma chordArcInterval_bound
    (C : CycleSupport V) (d : ℕ) (hbound : d + 1 ≤ C.length) :
    0 + (d + 1) ≤ C.length := by
  -- Removing the harmless zero offset leaves the supplied arc bound.
  omega

/-- Helper for Exercise 7.19: a chord interval of forward length at least two has at least three
vertices. -/
private lemma chordArcLength_ge_three (d : ℕ) (hd : 2 ≤ d) :
    3 ≤ d + 1 := by
  -- Adding the initial vertex turns at least two edges into at least three vertices.
  omega

/-- Helper for Exercise 7.19: an interval beginning at a chord endpoint and ending at the other
endpoint is a cycle support once the chord closes it. -/
private def chordArcCycleSupport
    (C : CycleSupport V) (i : Fin C.length) (d : ℕ)
    (hbound : d + 1 ≤ C.length) (hd : 2 ≤ d) : CycleSupport V where
  length := d + 1
  verts := cycleIntervalVerts C i 0 (d + 1) (chordArcInterval_bound C d hbound)
  length_ge_three := chordArcLength_ge_three d hd

/-- Helper for Exercise 7.19: the cyclic interval closed by a chord uses only edges of the
ambient graph. -/
private lemma chordArcCycleSupport_isContained
    (C : CycleSupport V) (hC : C.IsContainedIn G) (i : Fin C.length) (d : ℕ)
    (hbound : d + 1 ≤ C.length) (hd : 2 ≤ d)
    (hchord : G.Adj (C.verts i) (C.verts (((finRotate C.length) ^ d) i))) :
    (chordArcCycleSupport C i d hbound hd).IsContainedIn G := by
  rw [CycleSupport.isContainedIn_iff]
  dsimp only [chordArcCycleSupport]
  intro k
  by_cases hk : k.1 < d
  · have hadj := hC (((finRotate C.length) ^ k.1) i)
    have hadjRotate : G.Adj
        (C.verts (((finRotate C.length) ^ k.1) i))
        (C.verts (finRotate C.length (((finRotate C.length) ^ k.1) i))) := by
      simpa [finRotate_apply, Fin.add_def] using hadj
    have hnext :
        finRotate C.length (((finRotate C.length) ^ k.1) i) =
          ((finRotate C.length) ^ (k.1 + 1)) i := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [hnext] at hadjRotate
    have hsuccLt : k.1 + 1 < d + 1 := by omega
    simpa [cycleIntervalVerts, Fin.add_def, Nat.mod_eq_of_lt hsuccLt]
      using hadjRotate
  · have hkLast : k.1 = d := by omega
    have hkEq : k = Fin.last d := by
      apply Fin.ext
      simpa using hkLast
    rw [hkEq]
    simpa [cycleIntervalVerts, Fin.add_def]
      using hchord.symm

/-- Helper for Exercise 7.19: a cyclic interval has as many distinct vertices as exponents. -/
private lemma cycleIntervalSupport_vertexFinset_card
    (C : CycleSupport V) (i : Fin C.length) (a m : ℕ)
    (hbound : a + m ≤ C.length) :
    (cycleIntervalSupport C i a m hbound).vertexFinset.card = m := by
  -- The interval labelling is an embedding, so mapping `univ` preserves its cardinality.
  change (Finset.univ.map (cycleIntervalVerts C i a m hbound)).card = m
  rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Helper for Exercise 7.19: every bounded cyclic interval lies in the original cycle support.
-/
private lemma cycleIntervalSupport_vertexFinset_subset
    (C : CycleSupport V) (i : Fin C.length) (a m : ℕ)
    (hbound : a + m ≤ C.length) :
    (cycleIntervalSupport C i a m hbound).vertexFinset ⊆ C.vertexFinset := by
  -- Every interval label is visibly one of the original cycle labels.
  intro v hv
  rw [CyclicSupport.mem_vertexFinset_iff] at hv
  rcases hv with ⟨k, rfl⟩
  exact C.mem_vertexFinset_iff.mpr
    ⟨((finRotate C.length) ^ (a + k.1)) i, rfl⟩

/-- Helper for Exercise 7.19: two consecutive disjoint exponent intervals have disjoint vertex
sets in the full cyclic orbit. -/
private lemma cycleIntervalSupport_disjoint
    (C : CycleSupport V) (i : Fin C.length) (m₁ m₂ : ℕ)
    (hfirst : 0 + m₁ ≤ C.length) (hbound : m₁ + m₂ ≤ C.length) :
    Disjoint
      (cycleIntervalSupport C i 0 m₁ hfirst).vertexFinset
      (cycleIntervalSupport C i m₁ m₂ hbound).vertexFinset := by
  -- An intersection would equate exponents from the disjoint numerical ranges.
  rw [Finset.disjoint_left]
  intro v hv₁ hv₂
  rw [CyclicSupport.mem_vertexFinset_iff] at hv₁ hv₂
  change ∃ k : Fin m₁,
    (cycleIntervalVerts C i 0 m₁ hfirst) k = v at hv₁
  change ∃ l : Fin m₂,
    (cycleIntervalVerts C i m₁ m₂ hbound) l = v at hv₂
  rcases hv₁ with ⟨k, rfl⟩
  rcases hv₂ with ⟨l, hl⟩
  dsimp only [cycleIntervalSupport, cycleIntervalVerts] at hl
  have hklt : k.1 < C.length := by omega
  have hllt : m₁ + l.1 < C.length := by omega
  have hvertsEq :
      C.verts (((finRotate C.length) ^ k.1) i) =
        C.verts (((finRotate C.length) ^ (m₁ + l.1)) i) := by
    simpa only [cycleIntervalVerts, zero_add] using hl.symm
  have horbitEq :
      ((finRotate C.length) ^ k.1) i =
        ((finRotate C.length) ^ (m₁ + l.1)) i := by
    exact C.verts.injective hvertsEq
  have hpowers := finRotate_pow_apply_injective_below_length C i
    (a := k.1) (b := m₁ + l.1) hklt hllt
    horbitEq
  omega

/-- Helper for Exercise 7.19: two consecutive exponent intervals whose lengths sum to the cycle
length partition the original vertex support. -/
private lemma cycleIntervalSupport_union_eq_vertexFinset
    (C : CycleSupport V) (i : Fin C.length) (m₁ m₂ : ℕ)
    (hfirst : 0 + m₁ ≤ C.length) (hsecond : m₁ + m₂ ≤ C.length)
    (hlength : C.length = m₁ + m₂) :
    (cycleIntervalSupport C i 0 m₁ hfirst).vertexFinset ∪
        (cycleIntervalSupport C i m₁ m₂ hsecond).vertexFinset =
      C.vertexFinset := by
  -- The union is contained in the cycle and has the full cycle cardinality.
  have hsub :
      (cycleIntervalSupport C i 0 m₁ hfirst).vertexFinset ∪
          (cycleIntervalSupport C i m₁ m₂ hsecond).vertexFinset ⊆
        C.vertexFinset := by
    exact Finset.union_subset
      (cycleIntervalSupport_vertexFinset_subset C i 0 m₁ hfirst)
      (cycleIntervalSupport_vertexFinset_subset C i m₁ m₂ hsecond)
  have hdisjoint := cycleIntervalSupport_disjoint C i m₁ m₂ hfirst hsecond
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_union_of_disjoint hdisjoint,
    cycleIntervalSupport_vertexFinset_card,
    cycleIntervalSupport_vertexFinset_card]
  simpa [CycleSupport.vertexFinset, CyclicSupport.vertexFinset, hlength]

/-- Helper for Exercise 7.19: dividing the index of an even interval by two produces the index
of its consecutive pair. -/
private lemma evenIntervalPairIndex_lt (r : ℕ) (k : Fin (2 * r)) :
    k.1 / 2 < r := by
  -- Halving an index below `2 * r` produces an index below `r`.
  omega

/-- Helper for Exercise 7.19: the pair containing an index in an interval of length `2 * r`. -/
private def evenIntervalPairIndex (r : ℕ) (k : Fin (2 * r)) : Fin r :=
  ⟨k.1 / 2, evenIntervalPairIndex_lt r k⟩

/-- Helper for Exercise 7.19: an independent set selects at most one endpoint from each edge in
an even cyclic interval partitioned into consecutive pairs. -/
private lemma evenCycleIntervalSelectedIndices_card_le
    (C : CycleSupport V) (hC : C.IsContainedIn G) (i : Fin C.length)
    (a r : ℕ) (hbound : a + 2 * r ≤ C.length)
    (s : Finset V) (hs : G.IsIndepSet s) :
    (Finset.univ.filter fun k : Fin (2 * r) ↦
      (cycleIntervalVerts C i a (2 * r) hbound) k ∈ s).card ≤ r := by
  classical
  let A : Finset (Fin (2 * r)) :=
    Finset.univ.filter fun k : Fin (2 * r) ↦
      (cycleIntervalVerts C i a (2 * r) hbound) k ∈ s
  let pairIndex : {k // k ∈ A} → Fin r := fun k ↦ evenIntervalPairIndex r k.1
  have hpairInjective : Function.Injective pairIndex := by
    intro k l hpair
    apply Subtype.ext
    apply Fin.ext
    by_contra hkl
    have hkMem : (cycleIntervalVerts C i a (2 * r) hbound) k.1 ∈ s :=
      (Finset.mem_filter.mp k.2).2
    have hlMem : (cycleIntervalVerts C i a (2 * r) hbound) l.1 ∈ s :=
      (Finset.mem_filter.mp l.2).2
    have hquot : k.1.1 / 2 = l.1.1 / 2 := by
      simpa [pairIndex, evenIntervalPairIndex] using congrArg Fin.val hpair
    have hlt : k.1.1 < l.1.1 ∨ l.1.1 < k.1.1 := by omega
    rcases hlt with hlt | hlt
    · let p : Fin r := evenIntervalPairIndex r k.1
      have hkVal : k.1.1 = 2 * p.1 := by
        dsimp [p, evenIntervalPairIndex]
        omega
      have hlVal : l.1.1 = 2 * p.1 + 1 := by
        dsimp [p, evenIntervalPairIndex]
        omega
      have hadj := hC (((finRotate C.length) ^ (a + 2 * p.1)) i)
      have hadjRotate : G.Adj
          (C.verts (((finRotate C.length) ^ (a + 2 * p.1)) i))
          (C.verts
            (finRotate C.length (((finRotate C.length) ^ (a + 2 * p.1)) i))) := by
        simpa [finRotate_apply, Fin.add_def] using hadj
      have hnext :
          finRotate C.length (((finRotate C.length) ^ (a + 2 * p.1)) i) =
            ((finRotate C.length) ^ (a + (2 * p.1 + 1))) i := by
        have hExponent : a + (2 * p.1 + 1) = (a + 2 * p.1) + 1 := by omega
        rw [hExponent, pow_succ', Equiv.Perm.mul_apply]
      have hadj' : G.Adj
          ((cycleIntervalVerts C i a (2 * r) hbound) k.1)
          ((cycleIntervalVerts C i a (2 * r) hbound) l.1) := by
        rw [hnext] at hadjRotate
        simpa [cycleIntervalVerts, hkVal, hlVal] using hadjRotate
      have hne : k.1 ≠ l.1 := by
        intro heq
        exact hkl (congrArg Fin.val heq)
      exact (hs hkMem hlMem
        ((cycleIntervalVerts C i a (2 * r) hbound).injective.ne hne)) hadj'
    · let p : Fin r := evenIntervalPairIndex r l.1
      have hlVal : l.1.1 = 2 * p.1 := by
        dsimp [p, evenIntervalPairIndex]
        omega
      have hkVal : k.1.1 = 2 * p.1 + 1 := by
        dsimp [p, evenIntervalPairIndex]
        omega
      have hadj := hC (((finRotate C.length) ^ (a + 2 * p.1)) i)
      have hadjRotate : G.Adj
          (C.verts (((finRotate C.length) ^ (a + 2 * p.1)) i))
          (C.verts
            (finRotate C.length (((finRotate C.length) ^ (a + 2 * p.1)) i))) := by
        simpa [finRotate_apply, Fin.add_def] using hadj
      have hnext :
          finRotate C.length (((finRotate C.length) ^ (a + 2 * p.1)) i) =
            ((finRotate C.length) ^ (a + (2 * p.1 + 1))) i := by
        have hExponent : a + (2 * p.1 + 1) = (a + 2 * p.1) + 1 := by omega
        rw [hExponent, pow_succ', Equiv.Perm.mul_apply]
      have hadj' : G.Adj
          ((cycleIntervalVerts C i a (2 * r) hbound) l.1)
          ((cycleIntervalVerts C i a (2 * r) hbound) k.1) := by
        rw [hnext] at hadjRotate
        simpa [cycleIntervalVerts, hkVal, hlVal] using hadjRotate
      have hne : l.1 ≠ k.1 := by
        intro heq
        exact hkl (congrArg Fin.val heq.symm)
      exact (hs hlMem hkMem
        ((cycleIntervalVerts C i a (2 * r) hbound).injective.ne hne)) hadj'
  -- The pair-index injection sends every selected interval vertex into one of the `r` pairs.
  change A.card ≤ r
  calc
    A.card = Fintype.card {k // k ∈ A} := (Fintype.card_coe A).symm
    _ ≤ Fintype.card (Fin r) :=
      Fintype.card_le_of_injective pairIndex hpairInjective
    _ = r := Fintype.card_fin r

/-- Helper for Exercise 7.19: an independent set selects at most half the vertices of an odd
cycle, rounded down. -/
private lemma oddCycleSelectedIndices_card_le
    (C : CycleSupport V) (hC : C.IsContainedIn G) (hodd : Odd C.length)
    (s : Finset V) (hs : G.IsIndepSet s) :
    (Finset.univ.filter fun i : Fin C.length ↦ C.verts i ∈ s).card ≤
      (C.length - 1) / 2 := by
  classical
  let A : Finset (Fin C.length) :=
    Finset.univ.filter fun i : Fin C.length ↦ C.verts i ∈ s
  let σ : Equiv.Perm (Fin C.length) := finRotate C.length
  have hdisjoint : Disjoint A (A.image σ) := by
    -- A selected label and the successor of another selected label cannot coincide, since that
    -- would put both endpoints of a cycle edge in the independent set.
    rw [Finset.disjoint_left]
    intro i hiA hiImage
    rcases Finset.mem_image.mp hiImage with ⟨j, hjA, hji⟩
    have hiSelected : C.verts i ∈ s := (Finset.mem_filter.mp hiA).2
    have hjSelected : C.verts j ∈ s := (Finset.mem_filter.mp hjA).2
    have hjEdge : G.Adj (C.verts j) (C.verts (σ j)) := by
      simpa [σ, finRotate_apply, Fin.add_def] using hC j
    have hji' : σ j = i := by
      simpa using hji
    have hmove : σ j ≠ j := by
      exact Equiv.Perm.mem_support.mp <| by
        simp [σ, support_finRotate_of_le
          (le_trans (by decide : 2 ≤ 3) C.length_ge_three)]
    have hji_ne : j ≠ i := by
      intro hEq
      exact hmove (hji'.trans hEq.symm)
    exact (hs hjSelected hiSelected (C.verts.injective.ne hji_ne))
      (by simpa [hji'] using hjEdge)
  have hcardUnion : A.card + (A.image σ).card ≤ C.length := by
    calc
      A.card + (A.image σ).card = (A ∪ A.image σ).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
      _ = C.length := Fintype.card_fin C.length
  have hdouble : 2 * A.card ≤ C.length := by
    simpa [Finset.card_image_of_injective _ σ.injective, two_mul] using hcardUnion
  rcases hodd.exists_bit1 with ⟨q, hq⟩
  -- Oddness turns the doubled bound into the desired floor-half bound.
  change A.card ≤ (C.length - 1) / 2
  omega

/-- Helper for Exercise 7.19: the even powers shorter than half an odd cycle act injectively on
each cyclic label. -/
private lemma oddCycleEvenOrbit_injective
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    Function.Injective
      (fun k : Fin q ↦ ((finRotate C.length) ^ (2 * k.1)) i) := by
  let σ : Equiv.Perm (Fin C.length) := finRotate C.length
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hmove : σ i ≠ i := by
    exact Equiv.Perm.mem_support.mp <| by simp [hsupport]
  have horder : orderOf σ = C.length := by
    rw [hcycle.orderOf, hsupport, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  have hpows : σ ^ (2 * a.1) = σ ^ (2 * b.1) := by
    apply hcycle.pow_eq_pow_iff.mpr
    exact ⟨i, hmove, by simpa [σ] using hab⟩
  have hmod : 2 * a.1 ≡ 2 * b.1 [MOD C.length] := by
    rw [← horder]
    exact pow_eq_pow_iff_modEq.mp hpows
  have hexponents : 2 * a.1 = 2 * b.1 :=
    hmod.eq_of_lt_of_lt (by omega) (by omega)
  apply Fin.ext
  omega

/-- Helper for Exercise 7.19: two points in the short even orbit cannot be cyclic successors. -/
private lemma oddCycleEvenOrbit_not_successor
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) (a b : Fin q) :
    finRotate C.length (((finRotate C.length) ^ (2 * a.1)) i) ≠
      ((finRotate C.length) ^ (2 * b.1)) i := by
  let σ : Equiv.Perm (Fin C.length) := finRotate C.length
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hmove : σ i ≠ i := by
    exact Equiv.Perm.mem_support.mp <| by simp [hsupport]
  have horder : orderOf σ = C.length := by
    rw [hcycle.orderOf, hsupport, Finset.card_univ, Fintype.card_fin]
  intro hsuccessor
  have happly : (σ ^ (2 * a.1 + 1)) i = (σ ^ (2 * b.1)) i := by
    simpa [σ, pow_succ', Equiv.Perm.mul_apply] using hsuccessor
  have hpows : σ ^ (2 * a.1 + 1) = σ ^ (2 * b.1) := by
    apply hcycle.pow_eq_pow_iff.mpr
    exact ⟨i, hmove, happly⟩
  have hmod : 2 * a.1 + 1 ≡ 2 * b.1 [MOD C.length] := by
    rw [← horder]
    exact pow_eq_pow_iff_modEq.mp hpows
  have hexponents : 2 * a.1 + 1 = 2 * b.1 :=
    hmod.eq_of_lt_of_lt (by omega) (by omega)
  omega

/-- Helper for Exercise 7.19: the alternating maximum stable set beginning at `i` consists of
the first `q` even cyclic shifts of `i`. -/
private noncomputable def oddCycleAlternatingSet
    (C : CycleSupport V) (q : ℕ) (i : Fin C.length) : Finset V :=
  Finset.univ.image
    (fun k : Fin q ↦ C.verts (((finRotate C.length) ^ (2 * k.1)) i))

/-- Helper for Exercise 7.19: an alternating odd-cycle set has exactly `q` vertices. -/
private lemma oddCycleAlternatingSet_card
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    (oddCycleAlternatingSet C q i).card = q := by
  classical
  rw [oddCycleAlternatingSet]
  calc
    (Finset.univ.image
        (fun k : Fin q ↦ C.verts (((finRotate C.length) ^ (2 * k.1)) i))).card =
        (Finset.univ : Finset (Fin q)).card := by
      apply Finset.card_image_of_injective
      intro a b hab
      apply oddCycleEvenOrbit_injective C q hlength i
      exact C.verts.injective hab
    _ = q := Fintype.card_fin q

/-- Helper for Exercise 7.19: every alternating odd-cycle set is contained in the cycle support.
-/
private lemma oddCycleAlternatingSet_subset_vertexFinset
    (C : CycleSupport V) (q : ℕ) (i : Fin C.length) :
    oddCycleAlternatingSet C q i ⊆ C.vertexFinset := by
  classical
  intro v hv
  rcases Finset.mem_image.mp hv with ⟨k, -, rfl⟩
  exact C.mem_vertexFinset_iff.mpr
    ⟨((finRotate C.length) ^ (2 * k.1)) i, rfl⟩

/-- Helper for Exercise 7.19: alternating sets are independent when the containing odd cycle is
chordless. -/
private lemma oddCycleAlternatingSet_isIndepSet
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (hChordless : C.IsChordlessIn G) (i : Fin C.length) :
    G.IsIndepSet (oddCycleAlternatingSet C q i) := by
  classical
  have hlen_pos : 0 < C.length := lt_of_lt_of_le (by decide) C.length_ge_three
  -- Local instance justification (finite cyclic arithmetic): length positivity supplies the
  -- genuinely non-inferable NeZero instance required by cyclic_offset_eq_sub_val.
  letI : NeZero C.length := ⟨Nat.ne_of_gt hlen_pos⟩
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv huv
  rcases Finset.mem_image.mp hu with ⟨a, -, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨b, -, rfl⟩
  intro hadj
  rcases hChordless.2 _ _ hadj with hab | hba
  · have hnext := (cyclicOffset_eq_one_iff
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three) _ _).1 hab
    exact oddCycleEvenOrbit_not_successor C q hlength i a b hnext.symm
  · have hnext := (cyclicOffset_eq_one_iff
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three) _ _).1 hba
    exact oddCycleEvenOrbit_not_successor C q hlength i b a hnext.symm

/-- Helper for Exercise 7.19: the last even power on an odd cycle is the predecessor of the
starting index. -/
private lemma oddCycleEvenOrbit_endpoint_eq_prev
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    ((finRotate C.length) ^ (2 * q)) i = (finRotate C.length).symm i := by
  let σ : Equiv.Perm (Fin C.length) := finRotate C.length
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have horder : orderOf σ = C.length := by
    rw [hcycle.orderOf, hsupport, Finset.card_univ, Fintype.card_fin]
  have hpow : σ ^ (2 * q + 1) = 1 := by
    have hpowLength : σ ^ C.length = 1 := by
      simpa only [← horder] using pow_orderOf_eq_one σ
    simpa only [hlength] using hpowLength
  apply (σ.apply_eq_iff_eq_symm_apply).mp
  have happly := congrArg (fun τ : Equiv.Perm (Fin C.length) ↦ τ i) hpow
  simpa [σ, pow_succ', Equiv.Perm.mul_apply] using happly

/-- Helper for Exercise 7.19: advancing a twice-shifted start through an even power agrees with
advancing the exponent by one. -/
private lemma finRotate_evenPower_shift
    (C : CycleSupport V) (i : Fin C.length) (k : ℕ) :
    ((finRotate C.length) ^ (2 * k))
        ((finRotate C.length) (finRotate C.length i)) =
      ((finRotate C.length) ^ (2 * (k + 1))) i := by
  -- Powers of the same cyclic rotation commute, so the two successor steps join the exponent.
  rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add,
    Equiv.Perm.mul_apply, pow_two, Equiv.Perm.mul_apply]

/-- Helper for Exercise 7.19: adding the predecessor to one alternating set gives the same
finite set as adding the start to its two-step shift. -/
private lemma oddCycleAlternatingSet_insert_shift
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    insert (C.verts ((finRotate C.length).symm i)) (oddCycleAlternatingSet C q i) =
      insert (C.verts i)
        (oddCycleAlternatingSet C q ((finRotate C.length) (finRotate C.length i))) := by
  classical
  have hqPos : 0 < q := by
    have hthree : 3 ≤ 2 * q + 1 := by simpa only [← hlength] using C.length_ge_three
    omega
  have hend := oddCycleEvenOrbit_endpoint_eq_prev C q hlength i
  ext v
  simp only [Finset.mem_insert, oddCycleAlternatingSet, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro (hprev | ⟨k, hk⟩)
    · right
      let kLast : Fin q := ⟨q - 1, by omega⟩
      refine ⟨kLast, ?_⟩
      rw [hprev]
      apply congrArg C.verts
      rw [finRotate_evenPower_shift]
      have hlast : 2 * (kLast.1 + 1) = 2 * q := by
        dsimp [kLast]
        omega
      rw [hlast, hend]
    · rcases k with ⟨_ | k, hkLt⟩
      · left
        simpa using hk.symm
      · right
        refine ⟨⟨k, by omega⟩, ?_⟩
        rw [← hk]
        exact congrArg C.verts (finRotate_evenPower_shift C i k)
  · rintro (hstart | ⟨k, hk⟩)
    · right
      let kZero : Fin q := ⟨0, hqPos⟩
      refine ⟨kZero, ?_⟩
      simpa [kZero] using hstart.symm
    · by_cases hkLast : k.1 + 1 = q
      · left
        rw [← hk]
        apply congrArg C.verts
        rw [finRotate_evenPower_shift, hkLast, hend]
      · right
        refine ⟨⟨k.1 + 1, by omega⟩, ?_⟩
        rw [← hk]
        exact congrArg C.verts (finRotate_evenPower_shift C i k.1).symm

/-- Helper for Exercise 7.19: the predecessor endpoint is not already in the alternating set. -/
private lemma oddCycleAlternatingSet_prev_not_mem
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    C.verts ((finRotate C.length).symm i) ∉ oddCycleAlternatingSet C q i := by
  classical
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨k, -, hk⟩
  have horbit :
      ((finRotate C.length) ^ (2 * k.1)) i =
        ((finRotate C.length) ^ (2 * q)) i := by
    rw [oddCycleEvenOrbit_endpoint_eq_prev C q hlength i]
    exact C.verts.injective hk
  have hexponents := finRotate_pow_apply_injective_below_length C i
    (a := 2 * k.1) (b := 2 * q) (by omega) (by omega) horbit
  omega

/-- Helper for Exercise 7.19: the starting endpoint is omitted by the two-step shifted
alternating set. -/
private lemma oddCycleAlternatingSet_start_not_mem_shift
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    C.verts i ∉
      oddCycleAlternatingSet C q ((finRotate C.length) (finRotate C.length i)) := by
  classical
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨k, -, hk⟩
  have horbit :
      ((finRotate C.length) ^ (2 * k.1 + 2)) i =
        ((finRotate C.length) ^ 0) i := by
    simpa [pow_add, pow_two, Equiv.Perm.mul_apply] using C.verts.injective hk
  have hexponents := finRotate_pow_apply_injective_below_length C i
    (a := 2 * k.1 + 2) (b := 0) (by omega) (by omega) horbit
  omega

/-- Helper for Exercise 7.19: exchanging one endpoint between equally completed supports changes
their indicators by the corresponding coordinate difference. -/
private lemma stableSetIndicator_sub_eq_single_sub_single
    {A B : Finset V} {a b : V}
    (hab : a ≠ b) (haA : a ∈ A) (haB : a ∉ B) (hbA : b ∉ A) (hbB : b ∈ B)
    (hinsert : insert b A = insert a B) :
    stableSetIndicator A - stableSetIndicator B = Pi.single a 1 - Pi.single b 1 := by
  classical
  ext v
  by_cases hva : v = a
  · subst v
    simp [stableSetIndicator, haA, haB, hab]
  · by_cases hvb : v = b
    · subst v
      simp [stableSetIndicator, hbA, hbB, hab]
    · have hmem : v ∈ A ↔ v ∈ B := by
        have := Finset.ext_iff.mp hinsert v
        simpa [hva, hvb] using this
      simp [stableSetIndicator, Pi.single_apply, hva, hvb, hmem]

/-- Helper for Exercise 7.19: shifting an alternating set by two changes its indicator by the
start-minus-predecessor coordinate difference. -/
private lemma oddCycleAlternatingSet_indicator_sub_shift
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (i : Fin C.length) :
    stableSetIndicator (oddCycleAlternatingSet C q i) -
        stableSetIndicator
          (oddCycleAlternatingSet C q
            ((finRotate C.length) (finRotate C.length i))) =
      Pi.single (C.verts i) 1 -
        Pi.single (C.verts ((finRotate C.length).symm i)) 1 := by
  classical
  have hqPos : 0 < q := by
    have hthree : 3 ≤ 2 * q + 1 := by simpa only [← hlength] using C.length_ge_three
    omega
  have hstart : C.verts i ∈ oddCycleAlternatingSet C q i := by
    rw [oddCycleAlternatingSet, Finset.mem_image]
    let kZero : Fin q := ⟨0, hqPos⟩
    exact ⟨kZero, Finset.mem_univ _, by simp [kZero]⟩
  have hprev :
      C.verts ((finRotate C.length).symm i) ∈
        oddCycleAlternatingSet C q
          ((finRotate C.length) (finRotate C.length i)) := by
    have hinsert := oddCycleAlternatingSet_insert_shift C q hlength i
    have hleft :
        C.verts ((finRotate C.length).symm i) ∈
          insert (C.verts ((finRotate C.length).symm i))
            (oddCycleAlternatingSet C q i) := Finset.mem_insert_self _ _
    rw [hinsert] at hleft
    rcases Finset.mem_insert.mp hleft with hEq | hmem
    · have hmove : finRotate C.length i ≠ i := by
        exact Equiv.Perm.mem_support.mp <| by
          simp [support_finRotate_of_le (le_trans (by decide : 2 ≤ 3) C.length_ge_three)]
      have hprevNe :
          C.verts ((finRotate C.length).symm i) ≠ C.verts i := by
        apply C.verts.injective.ne
        intro hidx
        have hfixed := congrArg (finRotate C.length) hidx
        have hfixed' : i = finRotate C.length i := by
          simpa only [Equiv.apply_symm_apply] using hfixed
        exact hmove hfixed'.symm
      exact False.elim (hprevNe hEq)
    · exact hmem
  have hne : C.verts i ≠ C.verts ((finRotate C.length).symm i) := by
    apply C.verts.injective.ne
    intro hEq
    have hfixed := congrArg (finRotate C.length) hEq
    have hmove : finRotate C.length i ≠ i := by
      exact Equiv.Perm.mem_support.mp <| by
        simp [support_finRotate_of_le (le_trans (by decide : 2 ≤ 3) C.length_ge_three)]
    have hfixed' : finRotate C.length i = i := by
      simpa only [Equiv.apply_symm_apply] using hfixed
    exact hmove hfixed'
  exact stableSetIndicator_sub_eq_single_sub_single hne hstart
    (oddCycleAlternatingSet_start_not_mem_shift C q hlength i)
    (oddCycleAlternatingSet_prev_not_mem C q hlength i) hprev
    (oddCycleAlternatingSet_insert_shift C q hlength i)

/-- Helper for Exercise 7.19: every alternating set of an odd chordless cycle lies on its
odd-cycle equality face. -/
private lemma stableSetIndicator_oddCycleAlternatingSet_mem_face
    (C : CycleSupport V) (q : ℕ) (hlength : C.length = 2 * q + 1)
    (hChordless : C.IsChordlessIn G) (i : Fin C.length) :
    stableSetIndicator (oddCycleAlternatingSet C q i) ∈ oddCycleFace G C := by
  classical
  have hsub := oddCycleAlternatingSet_subset_vertexFinset C q i
  rw [mem_oddCycleFace_iff]
  refine ⟨⟨stableSetIndicator_mem_stableSetPolytope (G := G)
    (oddCycleAlternatingSet_isIndepSet (G := G) C q hlength hChordless i), ?_⟩, ?_⟩
  · rw [mem_zero_outside_iff]
    intro v hv
    exact stableSetIndicator_of_notMem (fun hmem ↦ hv (hsub hmem))
  · rw [support_sum_indicator_eq_card hsub, oddCycleAlternatingSet_card C q hlength i,
      odd_cycle_inequality_rhs_eq, hlength]
    norm_num

/-- Helper for Exercise 7.19: alternating tight sets span the full supported zero-sum direction
of a chordless odd cycle. -/
private theorem oddCycleFaceSpansSupportedZeroSum
    (C : CycleSupport V) (hodd : Odd C.length) (hChordless : C.IsChordlessIn G) :
    (oddCycleFace G C).Nonempty ∧
      Pi.spanSubset ℝ (↑C.vertexFinset : Set V) ⊓
          LinearMap.ker
            (stableSetDotProductLinearMap (stableSetIndicator C.vertexFinset)) ≤
        (affineSpan ℝ (oddCycleFace G C)).direction := by
  classical
  rcases hodd.exists_bit1 with ⟨q, hlength⟩
  have hlen_pos : 0 < C.length := lt_of_lt_of_le (by decide) C.length_ge_three
  -- Local instance justification (finite cyclic arithmetic): length positivity supplies the
  -- genuinely non-inferable NeZero instance required by cyclic_offset_eq_sub_val.
  letI : NeZero C.length := ⟨Nat.ne_of_gt hlen_pos⟩
  let σ : Equiv.Perm (Fin C.length) := finRotate C.length
  let τ : Equiv.Perm (Fin C.length) := σ⁻¹
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le
      (le_trans (by decide : 2 ≤ 3) C.length_ge_three)
  have hτCycle : τ.IsCycle := by
    simpa [τ] using hcycle.inv
  have hτSupport : τ.support = Finset.univ := by
    simpa [τ, Equiv.Perm.support_inv] using hsupport
  have hpoint : ∀ i,
      stableSetIndicator (oddCycleAlternatingSet C q i) ∈ oddCycleFace G C :=
    stableSetIndicator_oddCycleAlternatingSet_mem_face
      (G := G) C q hlength hChordless
  have hsteps : ∀ i,
      (Pi.single (C.verts i) (1 : ℝ) - Pi.single (C.verts (τ i)) 1 : V → ℝ) ∈
        (affineSpan ℝ (oddCycleFace G C)).direction := by
    intro i
    have hleft := subset_affineSpan ℝ (oddCycleFace G C) (hpoint i)
    have hright := subset_affineSpan ℝ (oddCycleFace G C)
      (hpoint ((finRotate C.length) (finRotate C.length i)))
    have hvsub := AffineSubspace.vsub_mem_direction hleft hright
    rw [vsub_eq_sub, oddCycleAlternatingSet_indicator_sub_shift C q hlength i] at hvsub
    simpa [τ, σ] using hvsub
  refine ⟨⟨stableSetIndicator (oddCycleAlternatingSet C q 0), hpoint 0⟩, ?_⟩
  simpa [CycleSupport.vertexFinset, CyclicSupport.vertexFinset] using
    supportedZeroSum_le_of_cyclicSteps C.verts τ 0
      (affineSpan ℝ (oddCycleFace G C)).direction hτCycle hτSupport hsteps

/-- Helper for Exercise 7.19: a chord whose forward arc has even edge length forces an
additional independent equality on the odd-cycle face, so that face cannot be a facet. -/
private theorem oddCycleFacet_not_of_evenChord
    (C : CycleSupport V) (hC : C.IsContainedIn G) (i : Fin C.length)
    (p r : ℕ) (hp : 0 < p) (hr : 0 < r)
    (hlength : C.length = 2 * p + 2 * r + 1)
    (hchord : G.Adj (C.verts i)
      (C.verts (((finRotate C.length) ^ (2 * p)) i))) :
    ¬ IsFacetOf
      (STAB(G) ∩ zero_outside C.vertexFinset)
      (oddCycleFace G C) := by
  classical
  have hArcBound : 2 * p + 1 ≤ C.length := by omega
  have hArcTwo : 2 ≤ 2 * p := by omega
  have hTailBound : (2 * p + 1) + 2 * r ≤ C.length := by omega
  have hFirstBound : 0 + (2 * p + 1) ≤ C.length := by omega
  let A : CycleSupport V :=
    chordArcCycleSupport C i (2 * p) hArcBound hArcTwo
  let U : CyclicSupport V :=
    cycleIntervalSupport C i (2 * p + 1) (2 * r) hTailBound
  let T : Finset V := A.vertexFinset
  let R : Finset V := U.vertexFinset
  have hArcContained : A.IsContainedIn G := by
    -- The original path supplies all interval edges and the given chord closes the last edge.
    exact chordArcCycleSupport_isContained (G := G) C hC i (2 * p)
      hArcBound hArcTwo hchord
  have hArcOdd : Odd A.length := by
    refine ⟨p, ?_⟩
    simp [A, chordArcCycleSupport, two_mul]
  have hDisjoint : Disjoint T R := by
    -- The arc occupies exponents `0,…,2p`, and the tail occupies the remaining exponents.
    simpa [T, R, A, U, chordArcCycleSupport] using
      cycleIntervalSupport_disjoint C i (2 * p + 1) (2 * r)
        hFirstBound hTailBound
  have hPartitionLength : C.length = (2 * p + 1) + 2 * r := by omega
  have hPartition : T ∪ R = C.vertexFinset := by
    simpa [T, R, A, U, chordArcCycleSupport] using
      cycleIntervalSupport_union_eq_vertexFinset C i (2 * p + 1) (2 * r)
        hFirstBound hTailBound hPartitionLength
  have hTValid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → T.sum x ≤ p := by
    intro x hx
    have hdot : stableSetIndicator T ⬝ᵥ x ≤ (p : ℝ) := by
      apply dotProductLeOfMemStableSetPolytope (G := G) (x := x) _ hx
      intro s hs
      rw [stableSetIndicator_dotProduct]
      have hcard := oddCycleSelectedIndices_card_le (G := G) A hArcContained hArcOdd s hs
      have hTSupport : T = A.toCyclicSupport.vertexFinset := rfl
      rw [hTSupport, cyclicSupport_sum_indicator_eq_card]
      have hhalf : (A.length - 1) / 2 = p := by
        simp [A, chordArcCycleSupport]
      rw [hhalf] at hcard
      exact_mod_cast hcard
    simpa [stableSetIndicator_dotProduct] using hdot
  have hRValid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → R.sum x ≤ r := by
    intro x hx
    have hdot : stableSetIndicator R ⬝ᵥ x ≤ (r : ℝ) := by
      apply dotProductLeOfMemStableSetPolytope (G := G) (x := x) _ hx
      intro s hs
      rw [stableSetIndicator_dotProduct]
      have hRSupport : R = U.vertexFinset := rfl
      rw [hRSupport, cyclicSupport_sum_indicator_eq_card]
      exact_mod_cast evenCycleIntervalSelectedIndices_card_le
        (G := G) C hC i (2 * p + 1) r hTailBound s hs
    simpa [stableSetIndicator_dotProduct] using hdot
  intro hFacet
  rcases (isFacetOf_iff.mp hFacet) with ⟨hfaceNonempty, -, hfacetRank⟩
  obtain ⟨x₀, hx₀⟩ := hfaceNonempty
  have hlevel : ∀ ⦃x : V → ℝ⦄, x ∈ oddCycleFace G C → T.sum x = p := by
    intro x hx
    have hxStab : x ∈ STAB(G) := hx.1.1
    have hTle := hTValid hxStab
    have hRle := hRValid hxStab
    have hsum : T.sum x + R.sum x = C.vertexFinset.sum x := by
      rw [← Finset.sum_union hDisjoint, hPartition]
    have hhalf : (C.length - 1) / 2 = p + r := by omega
    have htotal : C.vertexFinset.sum x = (p + r : ℕ) := by
      rw [hx.2, odd_cycle_inequality_rhs_eq, hhalf]
    rw [htotal] at hsum
    norm_num at hTle hRle hsum
    linarith
  have hsecondary :
      (affineSpan ℝ (oddCycleFace G C)).direction ≤
        LinearMap.ker
          (stableSetDotProductLinearMap (stableSetIndicator T)) := by
    apply affineSpan_direction_le_ker_of_forall_eq hx₀
    intro x hx
    simpa [stableSetDotProductLinearMap_apply, stableSetIndicator_dotProduct] using hlevel hx
  have hsupportNonempty : C.vertexFinset.Nonempty := by
    exact ⟨C.verts i, C.mem_vertexFinset_iff.mpr ⟨i, rfl⟩⟩
  let D : Submodule ℝ (V → ℝ) :=
    Pi.spanSubset ℝ (↑C.vertexFinset : Set V) ⊓
      LinearMap.ker
        (stableSetDotProductLinearMap (stableSetIndicator C.vertexFinset))
  have hupper : (affineSpan ℝ (oddCycleFace G C)).direction ≤ D := by
    exact equalitySliceDirection_le_supportZeroSum C.vertexFinset (STAB(G))
      (odd_cycle_inequality_rhs C) x₀ hx₀.2
  have hfaceRank :
      Module.finrank ℝ (affineSpan ℝ (oddCycleFace G C)).direction =
        C.vertexFinset.card - 1 := by
    have hambientRank := supportRestrictedStableSetPolytope_finrank (G := G) C.vertexFinset
    omega
  have hDRank : Module.finrank ℝ D = C.vertexFinset.card - 1 := by
    exact supportRestrictedZeroSum_finrank C.vertexFinset hsupportNonempty
  have hDirection : (affineSpan ℝ (oddCycleFace G C)).direction = D := by
    exact Submodule.eq_of_le_of_finrank_eq hupper (hfaceRank.trans hDRank.symm)
  have hTNonempty : 0 < 2 * p + 1 := by omega
  have hRNonempty : 0 < 2 * r := by omega
  let kT : Fin (2 * p + 1) := ⟨0, hTNonempty⟩
  let kR : Fin (2 * r) := ⟨0, hRNonempty⟩
  let a : V := C.verts i
  let b : V := C.verts (((finRotate C.length) ^ (2 * p + 1)) i)
  have haT : a ∈ T := by
    dsimp only [T, A]
    rw [CycleSupport.mem_vertexFinset_iff]
    refine ⟨kT, ?_⟩
    change C.verts (((finRotate C.length) ^ 0) i) = C.verts i
    simp
  have hbR : b ∈ R := by
    dsimp only [R, U]
    rw [CyclicSupport.mem_vertexFinset_iff]
    refine ⟨kR, ?_⟩
    change C.verts (((finRotate C.length) ^ ((2 * p + 1) + 0)) i) =
      C.verts (((finRotate C.length) ^ (2 * p + 1)) i)
    simp
  have hbT : b ∉ T := fun hb ↦ Finset.disjoint_left.mp hDisjoint hb hbR
  have haS : a ∈ C.vertexFinset := hPartition ▸ Finset.mem_union_left R haT
  have hbS : b ∈ C.vertexFinset := hPartition ▸ Finset.mem_union_right T hbR
  have hab : a ≠ b := by
    intro habEq
    have hzeroLt : 0 < C.length := by omega
    have htailLt : 2 * p + 1 < C.length := by omega
    have horbitEq :
        ((finRotate C.length) ^ 0) i =
          ((finRotate C.length) ^ (2 * p + 1)) i := by
      simpa [a, b] using C.verts.injective habEq
    have hpowers := finRotate_pow_apply_injective_below_length C i
      (a := 0) (b := 2 * p + 1) hzeroLt htailLt horbitEq
    omega
  let w : V → ℝ := Pi.single a 1 - Pi.single b 1
  have hwD : w ∈ D := by
    refine ⟨?_, ?_⟩
    · change w ∈ Pi.spanSubset ℝ (↑C.vertexFinset : Set V)
      rw [Pi.mem_spanSubset_iff]
      intro v hv
      have hva : v ≠ a := fun hva ↦ hv (hva ▸ haS)
      have hvb : v ≠ b := fun hvb ↦ hv (hvb ▸ hbS)
      simp [w, Pi.single_apply, hva, hvb]
    · change w ∈
        LinearMap.ker
          (stableSetDotProductLinearMap (stableSetIndicator C.vertexFinset))
      rw [LinearMap.mem_ker, stableSetDotProductLinearMap_apply,
        stableSetIndicator_dotProduct]
      simp [w, haS, hbS, hab]
  have hwDirection : w ∈ (affineSpan ℝ (oddCycleFace G C)).direction := by
    rw [hDirection]
    exact hwD
  have hwKernel := LinearMap.mem_ker.mp (hsecondary hwDirection)
  have hwEval :
      stableSetDotProductLinearMap (stableSetIndicator T) w = 1 := by
    rw [stableSetDotProductLinearMap_apply, stableSetIndicator_dotProduct]
    simp [w, haT, hbT, hab]
  linarith

/-- Helper for Exercise 7.19: an independent set in an induced antihole selects at most two
cyclic labels. -/
private lemma antiholeSelectedIndices_card_le_two
    (H : AntiholeSupport V) (hInd : H.IsInducedIn G)
    (s : Finset V) (hs : G.IsIndepSet s) :
    (Finset.univ.filter fun i : Fin H.length ↦ H.verts i ∈ s).card ≤ 2 := by
  classical
  have hlen_pos : 0 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
  -- Local instance justification (finite cyclic arithmetic): length positivity supplies the
  -- genuinely non-inferable NeZero instance required by cyclic_offset_eq_sub_val.
  letI : NeZero H.length := ⟨Nat.ne_of_gt hlen_pos⟩
  let A : Finset (Fin H.length) :=
    Finset.univ.filter fun i : Fin H.length ↦ H.verts i ∈ s
  by_contra hcard
  have hthree : 2 < A.card := Nat.lt_of_not_ge hcard
  rcases Finset.two_lt_card_iff.mp hthree with
    ⟨a, b, c, haA, hbA, hcA, hab, hac, hbc⟩
  have hselected : ∀ ⦃i : Fin H.length⦄, i ∈ A → H.verts i ∈ s := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hconsecutive : ∀ ⦃i j : Fin H.length⦄, i ∈ A → j ∈ A → i ≠ j →
      j = finRotate H.length i ∨ i = finRotate H.length j := by
    intro i j hiA hjA hij
    have hnotAdj : ¬ G.Adj (H.verts i) (H.verts j) :=
      hs (hselected hiA) (hselected hjA) (H.verts.injective.ne hij)
    have hsmall : cyclic_offset i j < 2 ∨ cyclic_offset j i < 2 := by
      by_contra hlarge
      push_neg at hlarge
      exact hnotAdj ((hInd i j).2 ⟨hij, hlarge.1, hlarge.2⟩)
    rcases hsmall with hijSmall | hjiSmall
    · left
      apply (cyclicOffset_eq_one_iff (m := H.length)
        (le_trans (by decide : 2 ≤ 5) H.length_ge_five) i j).1
      have hnonzero : cyclic_offset i j ≠ 0 := by
        simpa [cyclicOffset_eq_zero_iff] using hij
      omega
    · right
      apply (cyclicOffset_eq_one_iff (m := H.length)
        (le_trans (by decide : 2 ≤ 5) H.length_ge_five) j i).1
      have hnonzero : cyclic_offset j i ≠ 0 := by
        simpa [cyclicOffset_eq_zero_iff] using hij.symm
      omega
  rcases hconsecutive haA hbA hab with habNext | hbaNext
  · rcases hconsecutive haA hcA hac with hacNext | hcaNext
    · exact hbc (habNext.trans hacNext.symm)
    · have hbSecond : b = (finRotate H.length) ((finRotate H.length) c) := by
        calc
          b = finRotate H.length a := habNext
          _ = finRotate H.length (finRotate H.length c) := congrArg _ hcaNext
      have hoffsets := cyclicOffset_secondSuccessor_ge_two H.length_ge_five c
      have hbc' : (finRotate H.length) ((finRotate H.length) c) ≠ c := by
        simpa only [← hbSecond] using hbc
      have hbcAdj : G.Adj (H.verts b) (H.verts c) := by
        rw [hbSecond]
        exact (hInd _ _).2 ⟨hbc', hoffsets.1, hoffsets.2⟩
      exact (hs (hselected hbA) (hselected hcA) (H.verts.injective.ne hbc)) hbcAdj
  · rcases hconsecutive haA hcA hac with hacNext | hcaNext
    · have hcSecond : c = (finRotate H.length) ((finRotate H.length) b) := by
        calc
          c = finRotate H.length a := hacNext
          _ = finRotate H.length (finRotate H.length b) := congrArg _ hbaNext
      have hoffsets := cyclicOffset_secondSuccessor_ge_two H.length_ge_five b
      have hbc' : b ≠ (finRotate H.length) ((finRotate H.length) b) := by
        simpa only [← hcSecond] using hbc
      have hbcAdj : G.Adj (H.verts b) (H.verts c) := by
        rw [hcSecond]
        exact (hInd _ _).2 ⟨hbc', hoffsets.2, hoffsets.1⟩
      exact (hs (hselected hbA) (hselected hcA) (H.verts.injective.ne hbc)) hbcAdj
    · apply hbc
      exact (finRotate H.length).injective (hbaNext.symm.trans hcaNext)

/-- Helper for Exercise 7.19: the consecutive pair beginning at `i` is a canonical tight
stable set for the antihole inequality. -/
private noncomputable def antiholeTightPair
    (H : AntiholeSupport V) (i : Fin H.length) : Finset V :=
  {H.verts i, H.verts (finRotate H.length i)}

/-- Helper for Exercise 7.19: a consecutive labelled pair in an induced antihole is independent.
-/
private lemma antiholeTightPair_isIndepSet
    (H : AntiholeSupport V) (hInd : H.IsInducedIn G) (i : Fin H.length) :
    G.IsIndepSet (antiholeTightPair H i) := by
  classical
  have hlen_pos : 0 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
  -- Local instance justification (finite cyclic arithmetic): length positivity supplies the
  -- genuinely non-inferable NeZero instance required by cyclic_offset_eq_sub_val.
  letI : NeZero H.length := ⟨Nat.ne_of_gt hlen_pos⟩
  have hmove : finRotate H.length i ≠ i := by
    exact Equiv.Perm.mem_support.mp <| by
      simp [support_finRotate_of_le (le_trans (by decide : 2 ≤ 5) H.length_ge_five)]
  have hoffset : cyclic_offset i (finRotate H.length i) = 1 :=
    (cyclicOffset_eq_one_iff
      (le_trans (by decide : 2 ≤ 5) H.length_ge_five) i _).2 rfl
  have hnotAdj : ¬ G.Adj (H.verts i) (H.verts (finRotate H.length i)) := by
    rw [hInd]
    intro h
    omega
  rw [SimpleGraph.isIndepSet_iff]
  intro u hu v hv huv
  simp only [antiholeTightPair, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl
  · rcases hv with rfl | rfl
    · exact G.loopless.irrefl _
    · exact hnotAdj
  · rcases hv with rfl | rfl
    · simpa [SimpleGraph.adj_comm] using hnotAdj
    · exact G.loopless.irrefl _

/-- Helper for Exercise 7.19: every consecutive antihole pair lies on the equality face. -/
private lemma stableSetIndicator_antiholeTightPair_mem_face
    (H : AntiholeSupport V) (hInd : H.IsInducedIn G) (i : Fin H.length) :
    stableSetIndicator (antiholeTightPair H i) ∈ antiholeFace G H := by
  classical
  have hmove : finRotate H.length i ≠ i := by
    exact Equiv.Perm.mem_support.mp <| by
      simp [support_finRotate_of_le (le_trans (by decide : 2 ≤ 5) H.length_ge_five)]
  have hsub : antiholeTightPair H i ⊆ H.vertexFinset := by
    intro v hv
    simp only [antiholeTightPair, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact H.mem_vertexFinset_iff.mpr ⟨i, rfl⟩
    · exact H.mem_vertexFinset_iff.mpr ⟨finRotate H.length i, rfl⟩
  rw [mem_antiholeFace_iff]
  refine ⟨⟨stableSetIndicator_mem_stableSetPolytope (G := G)
    (antiholeTightPair_isIndepSet (G := G) H hInd i), ?_⟩, ?_⟩
  · rw [mem_zero_outside_iff]
    intro v hv
    exact stableSetIndicator_of_notMem (fun hmem ↦ hv (hsub hmem))
  · rw [support_sum_indicator_eq_card hsub]
    have hverts : H.verts i ≠ H.verts (finRotate H.length i) :=
      H.verts.injective.ne hmove.symm
    rw [antiholeTightPair, Finset.card_pair hverts]
    norm_num

/-- Helper for Exercise 7.19: shifting a consecutive antihole pair once changes its indicator by
the step-two coordinate difference. -/
private lemma antiholeTightPair_indicator_sub_shift
    (H : AntiholeSupport V) (i : Fin H.length) :
    stableSetIndicator (antiholeTightPair H i) -
        stableSetIndicator (antiholeTightPair H (finRotate H.length i)) =
      Pi.single (H.verts i) 1 -
        Pi.single (H.verts ((finRotate H.length) (finRotate H.length i))) 1 := by
  classical
  have hmove : finRotate H.length i ≠ i := by
    exact Equiv.Perm.mem_support.mp <| by
      simp [support_finRotate_of_le (le_trans (by decide : 2 ≤ 5) H.length_ge_five)]
  have hmoveNext :
      finRotate H.length (finRotate H.length i) ≠ finRotate H.length i := by
    exact (finRotate H.length).injective.ne hmove
  unfold antiholeTightPair
  rw [stableSetIndicatorPairOfNe (H.verts.injective.ne hmove.symm),
    stableSetIndicatorPairOfNe (H.verts.injective.ne hmoveNext.symm)]
  abel

/-- Helper for Exercise 7.19: consecutive tight pairs span the full supported zero-sum direction
of an induced odd antihole. -/
private theorem antiholeFaceSpansSupportedZeroSum
    (H : AntiholeSupport V) (hodd : Odd H.length) (hInd : H.IsInducedIn G) :
    (antiholeFace G H).Nonempty ∧
      Pi.spanSubset ℝ (↑H.vertexFinset : Set V) ⊓
          LinearMap.ker
            (stableSetDotProductLinearMap (stableSetIndicator H.vertexFinset)) ≤
        (affineSpan ℝ (antiholeFace G H)).direction := by
  classical
  have hlen_pos : 0 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
  -- Local instance justification (finite cyclic arithmetic): length positivity supplies the
  -- genuinely non-inferable NeZero instance required by cyclic_offset_eq_sub_val.
  letI : NeZero H.length := ⟨Nat.ne_of_gt hlen_pos⟩
  let σ : Equiv.Perm (Fin H.length) := finRotate H.length
  let τ : Equiv.Perm (Fin H.length) := σ ^ 2
  have hcycle : σ.IsCycle := by
    simpa [σ] using isCycle_finRotate_of_le
      (le_trans (by decide : 2 ≤ 5) H.length_ge_five)
  have hsupport : σ.support = Finset.univ := by
    simpa [σ] using support_finRotate_of_le
      (le_trans (by decide : 2 ≤ 5) H.length_ge_five)
  have horder : orderOf σ = H.length := by
    rw [hcycle.orderOf, hsupport, Finset.card_univ, Fintype.card_fin]
  have hτCycle : τ.IsCycle := by
    apply (hcycle.pow_iff).2
    rw [horder]
    exact Nat.coprime_two_left.mpr hodd
  have hτSupport : τ.support = Finset.univ := by
    dsimp [τ]
    have htwo : 2 < orderOf σ := by
      rw [horder]
      exact lt_of_lt_of_le (by decide : 2 < 5) H.length_ge_five
    rw [hcycle.support_pow_of_pos_of_lt_orderOf (by decide : 0 < 2) htwo, hsupport]
  have hpoint : ∀ i, stableSetIndicator (antiholeTightPair H i) ∈ antiholeFace G H :=
    stableSetIndicator_antiholeTightPair_mem_face (G := G) H hInd
  have hsteps : ∀ i,
      (Pi.single (H.verts i) (1 : ℝ) - Pi.single (H.verts (τ i)) 1 : V → ℝ) ∈
        (affineSpan ℝ (antiholeFace G H)).direction := by
    intro i
    have hleft := subset_affineSpan ℝ (antiholeFace G H) (hpoint i)
    have hright := subset_affineSpan ℝ (antiholeFace G H)
      (hpoint (finRotate H.length i))
    have hvsub := AffineSubspace.vsub_mem_direction hleft hright
    rw [vsub_eq_sub, antiholeTightPair_indicator_sub_shift H i] at hvsub
    simpa [τ, σ, pow_two, Equiv.Perm.mul_apply] using hvsub
  refine ⟨⟨stableSetIndicator (antiholeTightPair H 0), hpoint 0⟩, ?_⟩
  simpa [AntiholeSupport.vertexFinset, CyclicSupport.vertexFinset] using
    supportedZeroSum_le_of_cyclicSteps H.verts τ 0
      (affineSpan ℝ (antiholeFace G H)).direction hτCycle hτSupport hsteps

end FacetCombinatorialHelpers

section FacetStatements

variable [Fintype V]

/-- Exercise 7.19 (1). For a clique `K` of `G`, the clique inequality `∑_{v ∈ K} x_v ≤ 1` cuts
out a facet of `STAB(G)` if and only if `K` is a maximal clique. -/
theorem exercise_7_19_clique_inequality_facet_defining_iff_maximal_clique
    [Nonempty V] (K : Finset V) (hK : G.IsClique K) :
    IsFacetOf STAB(G) (cliqueFace G K) ↔
      Maximal G.IsClique K := by
  constructor
  · intro hFacet
    by_contra hmax
    have hmono :
        ∀ ⦃s t : Set V⦄, G.IsClique t → s ⊆ t → G.IsClique s := by
      intro s t ht hst
      exact ht.subset hst
    rcases Set.exists_insert_of_not_maximal (P := G.IsClique) hmono hK hmax with
      ⟨v, hvK, hK'⟩
    have hK'fin : G.IsClique (insert v K : Finset V) := by
      simpa using hK'
    have hsubset_coord :
        cliqueFace G K ⊆ coordinateZeroFace G v := by
      intro x hx
      rcases (mem_cliqueFace_iff G K x).1 hx with ⟨hxStab, hxK⟩
      have hK'le : (insert v K).sum x ≤ 1 :=
        clique_sum_le_one_of_mem_stableSetPolytope (G := G) (insert v K) hK'fin hxStab
      have hxv_nonneg : 0 ≤ x v :=
        coordinateNonneg_on_stableSetPolytope (G := G) v hxStab
      have hxv_zero : x v = 0 := by
        rw [Finset.sum_insert hvK] at hK'le
        linarith
      exact (mem_coordinateZeroFace_iff G v x).2 ⟨hxStab, hxv_zero⟩
    have hcoordFacet : IsFacetOf STAB(G) (coordinateZeroFace G v) :=
      coordinateZeroFace_isFacetOf (G := G) v
    have hpoly_dim :
        Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
      rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
        finrank_top, Module.finrank_fintype_fun_eq_card]
    have hEq :
        cliqueFace G K = coordinateZeroFace G v :=
      facet_eq_of_subset (V := V) (hP_dim := hpoly_dim) hFacet hcoordFacet hsubset_coord
    have hzero_coord : (0 : V → ℝ) ∈ coordinateZeroFace G v := by
      rw [mem_coordinateZeroFace_iff]
      refine ⟨?_, by simp⟩
      have h0 : stableSetIndicator (∅ : Finset V) ∈ STAB(G) :=
        stableSetIndicator_mem_stableSetPolytope (G := G) (by simp)
      simpa [stableSetIndicatorEmpty] using h0
    have hzero_face : (0 : V → ℝ) ∈ cliqueFace G K := by
      simpa [hEq] using hzero_coord
    have hsum_zero : K.sum (0 : V → ℝ) = 1 :=
      (mem_cliqueFace_iff G K 0).1 hzero_face |>.2
    simp at hsum_zero
  · intro hmax
    let F : Set (V → ℝ) := cliqueFace G K
    let c : V → ℝ := stableSetIndicator K
    have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → c ⬝ᵥ x ≤ 1 := by
      intro x hx
      simpa [c, stableSetIndicator_dotProduct] using
        clique_sum_le_one_of_mem_stableSetPolytope (G := G) K hK hx
    obtain ⟨W, hW_indep, hW_tight, hW_affine⟩ :=
      maximalCliqueWitnessFamily (G := G) hmax
    have hF_nonempty : F.Nonempty := by
      refine ⟨stableSetIndicator (W (Classical.choice ‹Nonempty V›)), ?_⟩
      rw [mem_cliqueFace_iff]
      refine ⟨stableSetIndicator_mem_stableSetPolytope (G := G) (hW_indep _), ?_⟩
      simpa using hW_tight _
    have hF_exposed : IsExposed ℝ STAB(G) F := by
      obtain ⟨v0⟩ := ‹Nonempty V›
      have hx0 : stableSetIndicator (W v0) ∈ STAB(G) :=
        stableSetIndicator_mem_stableSetPolytope (G := G) (hW_indep v0)
      have hx0_eq : c ⬝ᵥ stableSetIndicator (W v0) = 1 := by
        simpa [c, stableSetIndicator_dotProduct] using hW_tight v0
      have hEq :
          F = {x : V → ℝ | x ∈ STAB(G) ∧ c ⬝ᵥ x = 1} := by
        ext x
        simp [F, c, stableSetIndicator_dotProduct]
      rw [hEq]
      exact equalitySetIsExposed hvalid hx0 hx0_eq
    have hface_dim_lower :
        Fintype.card V - 1 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by
      let p : V → V → ℝ := fun v ↦ stableSetIndicator (W v)
      have hp_mem : Set.range p ⊆ F := by
        intro x hx
        rcases hx with ⟨v, rfl⟩
        rw [mem_cliqueFace_iff]
        refine ⟨stableSetIndicator_mem_stableSetPolytope (G := G) (hW_indep v), ?_⟩
        simpa [p] using hW_tight v
      have hspan_le : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ F :=
        affineSpan_mono ℝ hp_mem
      have hp_dim :
          Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = Fintype.card V - 1 := by
        rw [direction_affineSpan]
        exact hW_affine.finrank_vectorSpan <|
          (Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)).symm
      simpa [hp_dim] using
        Submodule.finrank_mono (AffineSubspace.direction_le hspan_le)
    have hdir_le :
        (affineSpan ℝ F).direction ≤ LinearMap.ker (stableSetDotProductLinearMap c) := by
      obtain ⟨v0⟩ := ‹Nonempty V›
      have hx0_eq : c ⬝ᵥ stableSetIndicator (W v0) = 1 := by
        simpa [c, stableSetIndicator_dotProduct] using hW_tight v0
      have hEq :
          F = {x : V → ℝ | x ∈ STAB(G) ∧ c ⬝ᵥ x = 1} := by
        ext x
        simp [F, c, stableSetIndicator_dotProduct]
      rw [hEq]
      exact equalitySetDirectionLeKer (P := STAB(G)) (c := c)
        (x₀ := stableSetIndicator (W v0)) (δ := 1) hx0_eq
    have hLinear_nonzero : stableSetDotProductLinearMap c ≠ 0 := by
      have hmono :
          ∀ ⦃s t : Set V⦄, G.IsClique t → s ⊆ t → G.IsClique s := by
        intro s t ht hst
        exact ht.subset hst
      have hmax_insert :=
        (Set.maximal_iff_forall_insert (P := G.IsClique) hmono).1 hmax
      have hK_nonempty : K.Nonempty := by
        by_contra hKempty
        have hKeq : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hKempty
        obtain ⟨v⟩ := ‹Nonempty V›
        have hsingle : G.IsClique (insert v (↑K : Set V)) := by
          simpa [hKeq] using
            (SimpleGraph.isClique_singleton (G := G) v)
        exact hmax_insert.2 v (by simpa [hKeq]) hsingle
      rcases hK_nonempty with ⟨v, hv⟩
      intro hzero
      have hvalue := congrArg (fun L : (V → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single v 1)) hzero
      simp [c, stableSetDotProductLinearMap, stableSetIndicator, hv] at hvalue
    have hface_dim_upper :
        Module.finrank ℝ (affineSpan ℝ F).direction ≤ Fintype.card V - 1 := by
      simpa [finrankKerEqCardSubOne (V := V) hLinear_nonzero] using
        Submodule.finrank_mono hdir_le
    have hpoly_dim :
        Module.finrank ℝ (affineSpan ℝ STAB(G)).direction = Fintype.card V := by
      rw [stableSetPolytopeAffineSpanEqTop (G := G), AffineSubspace.direction_top,
        finrank_top, Module.finrank_fintype_fun_eq_card]
    rw [isFacetOf_iff]
    refine ⟨hF_nonempty, hF_exposed, ?_⟩
    have hface_dim :
        Module.finrank ℝ (affineSpan ℝ F).direction = Fintype.card V - 1 :=
      le_antisymm hface_dim_upper hface_dim_lower
    calc
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 = Fintype.card V := by
        rw [hface_dim]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt Fintype.card_pos)
      _ = Module.finrank ℝ (affineSpan ℝ STAB(G)).direction := hpoly_dim.symm

/--
remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_7/ch7_sec7_7_exercise_7_19.lean
Exercise 7.19 (3). For an odd cycle support `C` contained in `G`, the odd-cycle inequality on
`C.vertexFinset` cuts out a facet of `STAB(G)` restricted to `C.vertexFinset` if and only if `C`
is chordless in `G`. -/
theorem exercise_7_19_odd_cycle_inequality_facet_defining_iff_chordless
    (C : CycleSupport V)
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    IsFacetOf
      (STAB(G) ∩ zero_outside C.vertexFinset)
      (oddCycleFace G C) ↔
      C.IsChordlessIn G := by
  classical
  constructor
  · intro hFacet
    refine ⟨hC, ?_⟩
    intro i j hadj
    by_cases hdOne : cyclic_offset i j = 1
    · exact Or.inl hdOne
    by_cases heOne : cyclic_offset j i = 1
    · exact Or.inr heOne
    exfalso
    have hij : i ≠ j := by
      intro hij
      subst j
      have hloop : ¬ G.Adj (C.verts i) (C.verts i) :=
        G.loopless.irrefl (C.verts i)
      exact hloop hadj
    have hzeroThree : 0 < 3 := by decide
    have hlenPos : 0 < C.length := lt_of_lt_of_le hzeroThree C.length_ge_three
    -- Local instance justification (finite cyclic arithmetic): length positivity supplies the
    -- genuinely non-inferable NeZero instance required by cyclic_offset_eq_sub_val.
    letI : NeZero C.length := ⟨Nat.ne_of_gt hlenPos⟩
    let d := cyclic_offset i j
    let e := cyclic_offset j i
    have hdge : 2 ≤ d := by
      have hdneZero : d ≠ 0 := by
        intro hdzero
        exact hij ((cyclicOffset_eq_zero_iff i j).1 hdzero)
      have hdneOne : d ≠ 1 := by
        exact hdOne
      omega
    have hege : 2 ≤ e := by
      have heneZero : e ≠ 0 := by
        intro hezero
        exact hij ((cyclicOffset_eq_zero_iff j i).1 hezero |>.symm)
      have heneOne : e ≠ 1 := by
        exact heOne
      omega
    have hsum : d + e = C.length := by
      exact cyclicOffset_add_reverse i j hij
    rcases hodd.exists_bit1 with ⟨q, hq⟩
    rcases Nat.even_or_odd d with hdEven | hdOdd
    · rcases hdEven with ⟨p, hpEq⟩
      have hpPos : 0 < p := by omega
      have hpq : p ≤ q := by omega
      let r := q - p
      have hrPos : 0 < r := by
        dsimp [r]
        omega
      have hlength : C.length = 2 * p + 2 * r + 1 := by
        dsimp [r]
        omega
      have hdEq : d = 2 * p := by omega
      have hendpoint : ((finRotate C.length) ^ (2 * p)) i = j := by
        rw [← hdEq]
        exact finRotate_pow_cyclicOffset i j
      have hchord : G.Adj (C.verts i)
          (C.verts (((finRotate C.length) ^ (2 * p)) i)) := by
        rwa [hendpoint]
      exact (oddCycleFacet_not_of_evenChord (G := G) C hC i p r hpPos hrPos
        hlength hchord) hFacet
    · rcases hdOdd.exists_bit1 with ⟨r, hrEq⟩
      have hrPos : 0 < r := by omega
      have hrq : r ≤ q := by omega
      let p := q - r
      have hpPos : 0 < p := by
        dsimp [p]
        omega
      have hlength : C.length = 2 * p + 2 * r + 1 := by
        dsimp [p]
        omega
      have heEq : e = 2 * p := by
        dsimp [p]
        omega
      have hendpoint : ((finRotate C.length) ^ (2 * p)) j = i := by
        rw [← heEq]
        exact finRotate_pow_cyclicOffset j i
      have hchord : G.Adj (C.verts j)
          (C.verts (((finRotate C.length) ^ (2 * p)) j)) := by
        rw [hendpoint]
        exact hadj.symm
      exact (oddCycleFacet_not_of_evenChord (G := G) C hC j p r hpPos hrPos
        hlength hchord) hFacet
  · intro hChordless
    have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) →
        C.vertexFinset.sum x ≤ odd_cycle_inequality_rhs C := by
      intro x hx
      have hdot : stableSetIndicator C.vertexFinset ⬝ᵥ x ≤
          odd_cycle_inequality_rhs C := by
        apply dotProductLeOfMemStableSetPolytope (G := G) (x := x) _ hx
        intro s hs
        have hsupportEq : C.vertexFinset = C.toCyclicSupport.vertexFinset := rfl
        rw [stableSetIndicator_dotProduct, hsupportEq,
          cyclicSupport_sum_indicator_eq_card, odd_cycle_inequality_rhs_eq]
        exact_mod_cast oddCycleSelectedIndices_card_le (G := G) C hC hodd s hs
      simpa [stableSetIndicator_dotProduct] using hdot
    have hsupportNonempty : C.vertexFinset.Nonempty := by
      have hzeroThree : 0 < 3 := by decide
      have hlenPos : 0 < C.length := lt_of_lt_of_le hzeroThree C.length_ge_three
      let i : Fin C.length := ⟨0, hlenPos⟩
      exact ⟨C.verts i, C.mem_vertexFinset_iff.mpr ⟨i, rfl⟩⟩
    obtain ⟨hfaceNonempty, hlower⟩ :=
      oddCycleFaceSpansSupportedZeroSum (G := G) C hodd hChordless
    -- Alternating tight stable sets provide all supported zero-sum directions, so the generic
    -- supported equality-slice criterion closes the forward implication.
    exact supportedStableSetEquality_isFacetOf (G := G) C.vertexFinset
      (odd_cycle_inequality_rhs C) hsupportNonempty hvalid hfaceNonempty hlower

/-- Exercise 7.19 (5). If an odd antihole support `H` is induced in `G`, then the antihole
inequality cuts out a facet of `STAB(G)` restricted to `H.vertexFinset`. -/
theorem exercise_7_19_antihole_inequality_facet_defining
    (H : AntiholeSupport V)
    (hodd : Odd H.length)
    (hInd : H.IsInducedIn G) :
    IsFacetOf
      (STAB(G) ∩ zero_outside H.vertexFinset)
      (antiholeFace G H) := by
  classical
  -- Route correction: consecutive tight pairs now supply the missing cyclic direction
  -- generators, so the generic supported-face shell applies directly.
  have hvalid : ∀ ⦃x : V → ℝ⦄, x ∈ STAB(G) → H.vertexFinset.sum x ≤ 2 := by
    intro x hx
    have hdot : stableSetIndicator H.vertexFinset ⬝ᵥ x ≤ 2 := by
      apply dotProductLeOfMemStableSetPolytope (G := G) (x := x) _ hx
      intro s hs
      rw [stableSetIndicator_dotProduct]
      rw [show H.vertexFinset = H.toCyclicSupport.vertexFinset by rfl,
        cyclicSupport_sum_indicator_eq_card]
      exact_mod_cast antiholeSelectedIndices_card_le_two (G := G) H hInd s hs
    simpa [stableSetIndicator_dotProduct] using hdot
  have hsupportNonempty : H.vertexFinset.Nonempty := by
    have hlen_pos : 0 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
    let i : Fin H.length := ⟨0, hlen_pos⟩
    exact ⟨H.verts i, H.mem_vertexFinset_iff.mpr ⟨i, rfl⟩⟩
  obtain ⟨hfaceNonempty, hlower⟩ :=
    antiholeFaceSpansSupportedZeroSum (G := G) H hodd hInd
  -- Validity, nonemptiness, and the generated zero-sum direction give codimension one.
  exact supportedStableSetEquality_isFacetOf (G := G) H.vertexFinset 2
    hsupportNonempty hvalid hfaceNonempty hlower

end FacetStatements

section ChvatalStatements

variable [Fintype V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Exercise 7.19 (2). For an odd cycle support `C` contained in `G`, the odd-cycle inequality on
`C.vertexFinset` is a Chvatal inequality for the edge relaxation `Q(G)`. -/
theorem exercise_7_19_odd_cycle_inequality_is_chvatal
    (C : CycleSupport V)
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    IsEdgeRelaxationChvatalInequality
      G
      (stableSetIndicator C.vertexFinset)
      (odd_cycle_inequality_rhs C) := by
  classical
  rw [isEdgeRelaxationChvatalInequality_iff]
  refine ⟨oddCycleEdgeMultiplier C, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The cycle certificate uses only nonnegative `1 / 2` edge multipliers.
    exact oddCycleEdgeMultiplier_nonneg (C := C)
  · -- Nonzero multipliers occur only on the actual cycle edges of `G`.
    exact oddCycleEdgeMultiplier_support (G := G) C hC
  · -- The slack function is identically zero.
    intro v
    simp
  · -- Each coefficient of the stable-set indicator is integral.
    intro v
    by_cases hv : v ∈ C.vertexFinset
    · exact ⟨1, by simp [stableSetIndicator, hv]⟩
    · exact ⟨0, by simp [stableSetIndicator, hv]⟩
  · -- The aggregated incidence vector is exactly the cycle-support indicator.
    simpa [oddCycleEdgeMultiplier_coefficients]
  · -- The floored total multiplier is the odd-cycle right-hand side.
    exact (oddCycleEdgeMultiplier_floor C hodd).symm

/-- Helper for Exercise 7.19: the forward web block starting at `i` contains exactly the labelled
vertices whose forward offset from `i` is at most `W.width`. -/
private noncomputable def webForwardBlock
    (W : WebSupport V) (i : Fin W.length) : Finset V :=
  (Finset.univ.filter fun j : Fin W.length ↦ cyclic_offset i j ≤ W.width).map W.verts

/-- Helper for Exercise 7.19: a labelled vertex lies in the forward block from `i` exactly when
its cyclic offset from `i` is at most `W.width`. -/
private lemma mem_webForwardBlock_iff
    (W : WebSupport V) (i j : Fin W.length) :
    W.verts j ∈ webForwardBlock W i ↔ cyclic_offset i j ≤ W.width := by
  -- Unfold the filtered map and use injectivity of `W.verts` to recover the index condition.
  simp [webForwardBlock]

/-- Helper for Exercise 7.19: two vertices lying in the same forward block have mutual cyclic
distance at most `W.width` in one direction. -/
private lemma cyclicOffset_le_of_common_webStart
    (W : WebSupport V) {i j k : Fin W.length}
    (hj : cyclic_offset i j ≤ W.width)
    (hk : cyclic_offset i k ≤ W.width) :
    cyclic_offset j k ≤ W.width ∨ cyclic_offset k j ≤ W.width := by
  have hlen_pos : 0 < W.length := lt_of_lt_of_le (by omega) W.width_bound
  letI : NeZero W.length := ⟨Nat.ne_of_gt hlen_pos⟩
  -- Normalize the two hypotheses first, then split on which difference is bounded.
  have hj' : (j - i).1 ≤ W.width := by
    simpa [cyclic_offset_eq_sub_val] using hj
  have hk' : (k - i).1 ≤ W.width := by
    simpa [cyclic_offset_eq_sub_val] using hk
  by_cases hkj : (k - j).1 ≤ W.width
  · left
    simpa [cyclic_offset_eq_sub_val] using hkj
  · right
    have hjk : (j - k).1 ≤ W.width := by
      fin_omega
    simpa [cyclic_offset_eq_sub_val] using hjk

/-- Helper for Exercise 7.19: each forward web block is a clique of `G` when `W` is contained in
`G`. -/
private lemma webForwardBlock_isClique
    (W : WebSupport V) (hW : W.IsContainedIn G) (i : Fin W.length) :
    G.IsClique (webForwardBlock W i) := by
  -- Compare two block vertices through their common start index `i`, then invoke the web
  -- adjacency rule on the resulting bounded cyclic distance.
  intro a ha b hb hab
  rcases Finset.mem_map.mp ha with ⟨j, hj, rfl⟩
  rcases Finset.mem_map.mp hb with ⟨k, hk, rfl⟩
  have hjle : cyclic_offset i j ≤ W.width := by
    simpa using (Finset.mem_filter.mp hj).2
  have hkle : cyclic_offset i k ≤ W.width := by
    simpa using (Finset.mem_filter.mp hk).2
  have hjk :
      cyclic_offset j k ≤ W.width ∨ cyclic_offset k j ≤ W.width :=
    cyclicOffset_le_of_common_webStart (W := W) hjle hkle
  have hne : j ≠ k := by
    intro hEq
    apply hab
    simpa [hEq]
  exact hW j k hne hjk

/-- Helper for Exercise 7.19: vertices outside `W.vertexFinset` do not belong to any forward web
block. -/
private lemma not_mem_webForwardBlock_of_not_vertex
    (W : WebSupport V) {v : V} (hv : v ∉ W.vertexFinset) (i : Fin W.length) :
    v ∉ webForwardBlock W i := by
  -- Every block vertex is one of the labelled vertices of `W`.
  intro hmem
  rcases Finset.mem_map.mp hmem with ⟨j, -, hj⟩
  exact hv ((WebSupport.mem_vertexFinset_iff W).2 ⟨j, hj⟩)

/-- Helper for Exercise 7.19: the web Chvatal certificate assigns multiplier `1 / (k + 1)` to
each forward block occurrence. -/
private noncomputable def webForwardBlockMultiplier
    (W : WebSupport V) : Finset V → ℝ :=
  fun K ↦ ∑ i : Fin W.length, if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0

/-- Helper for Exercise 7.19: the web block multipliers are coordinatewise nonnegative. -/
private lemma webForwardBlockMultiplier_nonneg
    (W : WebSupport V) :
    ∀ K : Finset V, 0 ≤ webForwardBlockMultiplier W K := by
  have hconst_nonneg : 0 ≤ (1 / (W.width + 1 : ℝ)) := by
    have hden_pos : (0 : ℝ) < W.width + 1 := by
      positivity
    positivity
  intro K
  -- Every indexed contribution is either `0` or the positive constant `1 / (k + 1)`.
  refine Finset.sum_nonneg ?_
  intro i hi
  by_cases hEq : K = webForwardBlock W i
  · simpa [hEq] using hconst_nonneg
  · simp [webForwardBlockMultiplier, hEq]

/-- Helper for Exercise 7.19: a nonzero web multiplier can only occur on a clique of `G`. -/
private lemma webForwardBlockMultiplier_support
    (W : WebSupport V) (hW : W.IsContainedIn G) :
    ∀ K : Finset V, webForwardBlockMultiplier W K ≠ 0 → G.IsClique K := by
  intro K hK
  by_contra hnotClique
  have hnoMatch : ∀ i : Fin W.length, K ≠ webForwardBlock W i := by
    intro i hEq
    apply hnotClique
    simpa [hEq] using webForwardBlock_isClique (G := G) W hW i
  have hzero : webForwardBlockMultiplier W K = 0 := by
    simp [webForwardBlockMultiplier, hnoMatch]
  exact hK hzero

/-- Helper for Exercise 7.19: for a fixed start index `i`, summing over all clique variables
collapses to the single forward block `webForwardBlock W i`. -/
private lemma webForwardBlockMultiplier_inner
    (W : WebSupport V) (i : Fin W.length) (v : V) :
    ∑ K : Finset V,
      (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
        (if v ∈ K then 1 else 0) =
      if v ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
  by_cases hmem : v ∈ webForwardBlock W i
  · -- Only the exact forward block contributes, and there it contributes the constant multiplier.
    rw [Finset.sum_eq_single (webForwardBlock W i)]
    · simp [hmem]
    · intro K hK hne
      simp [hne]
    · simp
  · -- If `v` is outside the block, every clique term vanishes.
    have hsum :
        (∑ K : Finset V,
          (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
            (if v ∈ K then 1 else 0)) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro K hK
      by_cases hEq : K = webForwardBlock W i
      · simp [hEq, hmem]
      · simp [hEq]
    simpa [hmem] using hsum

/-- Helper for Exercise 7.19: a labelled web vertex receives total coefficient one from the
forward-block multipliers. -/
private lemma webForwardBlockCoefficientAtLabel
    (W : WebSupport V) (j : Fin W.length) :
    ∑ i : Fin W.length,
      (if W.verts j ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) = 1 := by
  have hden_ne : (W.width + 1 : ℝ) ≠ 0 := by
    positivity
  -- Rewrite the direct coefficient sum to the filtered starts containing `j`.
  calc
    ∑ i : Fin W.length,
        (if W.verts j ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0)
      = Finset.sum
          (((Finset.univ : Finset (Fin W.length)).filter
            fun i : Fin W.length ↦ cyclic_offset i j ≤ W.width))
          (fun _ : Fin W.length ↦ (1 / (W.width + 1 : ℝ))) := by
            simpa [mem_webForwardBlock_iff] using
              (Finset.sum_filter
                (s := (Finset.univ : Finset (Fin W.length)))
                (p := fun i : Fin W.length ↦ cyclic_offset i j ≤ W.width)
                (f := fun _ : Fin W.length ↦ (1 / (W.width + 1 : ℝ)))).symm
    _ = ∑ i : {i : Fin W.length // cyclic_offset i j ≤ W.width},
          (1 / (W.width + 1 : ℝ)) := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin W.length)))
                (p := fun i : Fin W.length ↦ cyclic_offset i j ≤ W.width)
                (f := fun _ : Fin W.length ↦ (1 / (W.width + 1 : ℝ)))).symm
    _ = (W.width + 1 : ℝ) * (1 / (W.width + 1 : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, webForwardBlockStartCount (W := W) j]
    _ = 1 := by
          field_simp [hden_ne]

/-- Helper for Exercise 7.19: the aggregated web block coefficients equal the indicator of the
web support. -/
private lemma webForwardBlockMultiplier_coefficients
    (W : WebSupport V) :
    (fun v ↦ ∑ K : Finset V,
      webForwardBlockMultiplier W K * (if v ∈ K then 1 else 0)) =
      stableSetIndicator W.vertexFinset := by
  classical
  funext v
  by_cases hv : v ∈ W.vertexFinset
  · rcases (WebSupport.mem_vertexFinset_iff W).1 hv with ⟨j, rfl⟩
    -- For a support vertex, the coefficient is the constant block weight times the number of
    -- starts whose forward block contains that vertex.
    calc
      ∑ K : Finset V, webForwardBlockMultiplier W K * (if W.verts j ∈ K then 1 else 0)
          = ∑ K : Finset V,
              (∑ i : Fin W.length,
                (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
                  (if W.verts j ∈ K then 1 else 0)) := by
                simp [webForwardBlockMultiplier, Finset.mul_sum]
      _ = ∑ i : Fin W.length, ∑ K : Finset V,
            (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
              (if W.verts j ∈ K then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin W.length,
            if W.verts j ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact webForwardBlockMultiplier_inner (W := W) i (W.verts j)
      _ = 1 := webForwardBlockCoefficientAtLabel (W := W) j
      _ = stableSetIndicator W.vertexFinset (W.verts j) := by
            simp [stableSetIndicator, WebSupport.mem_vertexFinset_iff]
  · -- Outside the support every forward block term vanishes, so the coefficient is zero.
    have hzero :
        ∑ i : Fin W.length,
          (if v ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [not_mem_webForwardBlock_of_not_vertex (W := W) hv i]
    calc
      ∑ K : Finset V, webForwardBlockMultiplier W K * (if v ∈ K then 1 else 0)
          = ∑ K : Finset V,
              (∑ i : Fin W.length,
                (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
                  (if v ∈ K then 1 else 0)) := by
                simp [webForwardBlockMultiplier, Finset.mul_sum]
      _ = ∑ i : Fin W.length, ∑ K : Finset V,
            (if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0) *
              (if v ∈ K then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin W.length,
            if v ∈ webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact webForwardBlockMultiplier_inner (W := W) i v
      _ = 0 := hzero
      _ = stableSetIndicator W.vertexFinset v := by
            simp [stableSetIndicator, hv]

/-- Helper for Exercise 7.19: the total web block multiplier is the constant multiplier summed
over all labelled starts. -/
private lemma webForwardBlockMultiplier_sum
    (W : WebSupport V) :
    ∑ K : Finset V, webForwardBlockMultiplier W K =
      ∑ i : Fin W.length, (1 / (W.width + 1 : ℝ)) := by
  -- Swap the sums and collapse each inner singleton over `Finset V`.
  calc
    ∑ K : Finset V, webForwardBlockMultiplier W K
        = ∑ K : Finset V,
            ∑ i : Fin W.length,
              if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
              rfl
    _ = ∑ i : Fin W.length, ∑ K : Finset V,
          if K = webForwardBlock W i then (1 / (W.width + 1 : ℝ)) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin W.length, (1 / (W.width + 1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp

/-- Helper for Exercise 7.19: the `a`-th positive even cyclic offset used in the odd antihole
clique certificate. -/
private def antiholeShift
    (H : AntiholeSupport V) (a : Fin ((H.length - 1) / 2)) : Fin H.length :=
  ⟨2 * (a.1 + 1), by
    -- The `((H.length - 1) / 2)` choices give exactly the positive even offsets below `H.length`.
    have ha : a.1 < (H.length - 1) / 2 := a.2
    omega⟩

/-- Helper for Exercise 7.19: the alternating clique starting at `i` consists of the labelled
vertices at positive even offsets from `i`. -/
private noncomputable def antiholeAlternatingClique
    (H : AntiholeSupport V) (i : Fin H.length) : Finset V :=
  Finset.univ.image fun a : Fin ((H.length - 1) / 2) ↦ H.verts (i + antiholeShift H a)

/-- Helper for Exercise 7.19: a labelled vertex belongs to the alternating antihole clique
starting at `i` exactly when it is reached by one of the chosen even offsets. -/
private lemma mem_antiholeAlternatingClique_iff
    (H : AntiholeSupport V) (i j : Fin H.length) :
    H.verts j ∈ antiholeAlternatingClique H i ↔
      ∃ a : Fin ((H.length - 1) / 2), i + antiholeShift H a = j := by
  -- Unfold the image owner and use injectivity of the antihole labelling.
  constructor
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨a, -, ha⟩
    exact ⟨a, H.verts.injective ha⟩
  · rintro ⟨a, rfl⟩
    exact Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩

/-- Helper for Exercise 7.19: the positive even offsets used in the antihole certificate are
pairwise distinct. -/
private lemma antiholeShift_injective
    (H : AntiholeSupport V) :
    Function.Injective (antiholeShift H) := by
  intro a b hab
  apply Fin.ext
  have hval := congrArg Fin.val hab
  simp [antiholeShift] at hval
  omega

/-- Helper for Exercise 7.19: translating both indices by the same cyclic start does not change
their forward cyclic offset. -/
private lemma cyclic_offset_add_left {m : ℕ} [NeZero m]
    (i j k : Fin m) :
    cyclic_offset (i + j) (i + k) = cyclic_offset j k := by
  -- Move the comparison entirely to modular subtraction in `Fin m`.
  rw [cyclic_offset_eq_sub_val, cyclic_offset_eq_sub_val]
  exact congrArg Fin.val (by abel : (i + k) - (i + j) = k - j)

/-- Helper for Exercise 7.19: each alternating antihole clique is a clique of `G` under the
contained-antihole hypothesis. -/
private lemma antiholeAlternatingClique_isClique
    (H : AntiholeSupport V) (hH : H.IsContainedIn G) (i : Fin H.length) :
    G.IsClique (antiholeAlternatingClique H i) := by
  have hlen_pos : 0 < H.length :=
    lt_of_lt_of_le (by decide : 0 < 5) H.length_ge_five
  letI : NeZero H.length := ⟨Nat.ne_of_gt hlen_pos⟩
  intro u hu v hv huv
  rcases Finset.mem_image.mp hu with ⟨a, -, rfl⟩
  rcases Finset.mem_image.mp hv with ⟨b, -, rfl⟩
  have hab : a ≠ b := by
    intro hab
    apply huv
    simp [hab]
  have hab_idx :
      i + antiholeShift H a ≠ i + antiholeShift H b := by
    intro hij
    apply huv
    simp [hij]
  have hforw_shift :
      2 ≤ cyclic_offset (antiholeShift H a) (antiholeShift H b) := by
    rw [cyclic_offset_eq_sub_val]
    simp [antiholeShift]
    fin_omega
  have hback_shift :
      2 ≤ cyclic_offset (antiholeShift H b) (antiholeShift H a) := by
    rw [cyclic_offset_eq_sub_val]
    simp [antiholeShift]
    fin_omega
  have hforw :
      2 ≤ cyclic_offset (i + antiholeShift H a) (i + antiholeShift H b) := by
    rw [cyclic_offset_add_left]
    exact hforw_shift
  have hback :
      2 ≤ cyclic_offset (i + antiholeShift H b) (i + antiholeShift H a) := by
    rw [cyclic_offset_add_left]
    exact hback_shift
  exact hH (i + antiholeShift H a) (i + antiholeShift H b) hab_idx hforw hback

/-- Helper for Exercise 7.19: vertices outside `H.vertexFinset` do not belong to any alternating
antihole clique. -/
private lemma not_mem_antiholeAlternatingClique_of_not_vertex
    (H : AntiholeSupport V) {v : V} (hv : v ∉ H.vertexFinset) (i : Fin H.length) :
    v ∉ antiholeAlternatingClique H i := by
  -- Every alternating clique vertex is one of the labelled vertices of `H`.
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨a, -, ha⟩
  exact hv ((AntiholeSupport.mem_vertexFinset_iff H).2 ⟨i + antiholeShift H a, ha⟩)

/-- Helper for Exercise 7.19: exactly `((H.length - 1) / 2)` cyclic starts place the labelled
vertex `j` inside an alternating antihole clique. -/
private lemma antiholeAlternatingCliqueStartCount
    (H : AntiholeSupport V) (j : Fin H.length) :
    Fintype.card {i : Fin H.length // H.verts j ∈ antiholeAlternatingClique H i} =
      (H.length - 1) / 2 := by
  classical
  have hlen_pos : 0 < H.length := by
    exact lt_of_lt_of_le (by decide : 0 < 5) H.length_ge_five
  letI : NeZero H.length := ⟨Nat.ne_of_gt hlen_pos⟩
  let f : Fin ((H.length - 1) / 2) →
      {i : Fin H.length // H.verts j ∈ antiholeAlternatingClique H i} :=
    fun a ↦
      ⟨j - antiholeShift H a, by
        -- The translated start reaches `j` by the chosen positive even offset `a`.
        refine (mem_antiholeAlternatingClique_iff H (j - antiholeShift H a) j).2 ?_
        refine ⟨a, ?_⟩
        abel⟩
  have hf_bij : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval : (f a).1 = (f b).1 := congrArg Subtype.val hab
      have hshift : antiholeShift H a = antiholeShift H b := by
        have h := congrArg (fun t : Fin H.length ↦ j - t) hval
        simpa [f] using h
      exact antiholeShift_injective (H := H) hshift
    · intro i
      rcases (mem_antiholeAlternatingClique_iff H i.1 j).1 i.2 with ⟨a, ha⟩
      refine ⟨a, ?_⟩
      apply Subtype.ext
      have h := congrArg (fun t : Fin H.length ↦ t - antiholeShift H a) ha
      simpa [f] using h.symm
  simpa using (Fintype.card_congr (Equiv.ofBijective f hf_bij)).symm

/-- Helper for Exercise 7.19: the antihole Chvátal certificate assigns the constant multiplier
`2 / (H.length - 1)` to each alternating clique occurrence. -/
private noncomputable def antiholeAlternatingCliqueMultiplier
    (H : AntiholeSupport V) : Finset V → ℝ :=
  fun K ↦ ∑ i : Fin H.length,
    if K = antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0

/-- Helper for Exercise 7.19: the alternating-antihole clique multipliers are coordinatewise
nonnegative. -/
private lemma antiholeAlternatingCliqueMultiplier_nonneg
    (H : AntiholeSupport V) :
    ∀ K : Finset V, 0 ≤ antiholeAlternatingCliqueMultiplier H K := by
  have hconst_nonneg : 0 ≤ (2 / (H.length - 1 : ℝ)) := by
    have hlen_one_le : (1 : ℝ) ≤ H.length := by
      exact_mod_cast (le_trans (by decide : 1 ≤ 5) H.length_ge_five)
    have hden_nonneg : 0 ≤ (H.length : ℝ) - 1 := by
      linarith
    exact div_nonneg (by norm_num) hden_nonneg
  intro K
  refine Finset.sum_nonneg ?_
  intro i hi
  by_cases hEq : K = antiholeAlternatingClique H i
  · simpa [hEq] using hconst_nonneg
  · simp [antiholeAlternatingCliqueMultiplier, hEq]

/-- Helper for Exercise 7.19: a nonzero alternating-antihole multiplier can only occur on a
clique of `G`. -/
private lemma antiholeAlternatingCliqueMultiplier_support
    (H : AntiholeSupport V) (hH : H.IsContainedIn G) :
    ∀ K : Finset V, antiholeAlternatingCliqueMultiplier H K ≠ 0 → G.IsClique K := by
  intro K hK
  by_contra hnotClique
  have hnoMatch : ∀ i : Fin H.length, K ≠ antiholeAlternatingClique H i := by
    intro i hEq
    apply hnotClique
    simpa [hEq] using antiholeAlternatingClique_isClique (G := G) H hH i
  have hzero : antiholeAlternatingCliqueMultiplier H K = 0 := by
    simp [antiholeAlternatingCliqueMultiplier, hnoMatch]
  exact hK hzero

/-- Helper for Exercise 7.19: for a fixed start index `i`, summing over all clique variables
collapses to the single alternating clique `antiholeAlternatingClique H i`. -/
private lemma antiholeAlternatingCliqueMultiplier_inner
    (H : AntiholeSupport V) (i : Fin H.length) (v : V) :
    ∑ K : Finset V,
      (if K = antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0) *
        (if v ∈ K then 1 else 0) =
      if v ∈ antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0 := by
  by_cases hmem : v ∈ antiholeAlternatingClique H i
  · rw [Finset.sum_eq_single (antiholeAlternatingClique H i)]
    · simp [hmem]
    · intro K hK hne
      simp [hne]
    · simp
  · have hsum :
      (∑ K : Finset V,
        (if K = antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0) *
          (if v ∈ K then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro K hK
        by_cases hEq : K = antiholeAlternatingClique H i
        · simp [hEq, hmem]
        · simp [hEq]
    simpa [hmem] using hsum

/-- Helper for Exercise 7.19: a labelled antihole vertex receives total coefficient one from the
alternating-clique multipliers. -/
private lemma antiholeAlternatingCliqueCoefficientAtLabel
    (H : AntiholeSupport V) (hodd : Odd H.length) (j : Fin H.length) :
    ∑ i : Fin H.length,
      (if H.verts j ∈ antiholeAlternatingClique H i then
        (2 / (H.length - 1 : ℝ)) else 0) = 1 := by
  have hden_ne : (H.length - 1 : ℝ) ≠ 0 := by
    have hlen_gt_one : (1 : ℝ) < H.length := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 5) H.length_ge_five)
    linarith
  calc
    ∑ i : Fin H.length,
        (if H.verts j ∈ antiholeAlternatingClique H i then
          (2 / (H.length - 1 : ℝ)) else 0)
      = Finset.sum
          (((Finset.univ : Finset (Fin H.length)).filter
            fun i : Fin H.length ↦ H.verts j ∈ antiholeAlternatingClique H i))
          (fun _ : Fin H.length ↦ (2 / (H.length - 1 : ℝ))) := by
            simpa using
              (Finset.sum_filter
                (s := (Finset.univ : Finset (Fin H.length)))
                (p := fun i : Fin H.length ↦ H.verts j ∈ antiholeAlternatingClique H i)
                (f := fun _ : Fin H.length ↦ (2 / (H.length - 1 : ℝ)))).symm
    _ = ∑ i : {i : Fin H.length // H.verts j ∈ antiholeAlternatingClique H i},
          (2 / (H.length - 1 : ℝ)) := by
            simpa using
              (Finset.sum_subtype_eq_sum_filter
                (s := (Finset.univ : Finset (Fin H.length)))
                (p := fun i : Fin H.length ↦ H.verts j ∈ antiholeAlternatingClique H i)
                (f := fun _ : Fin H.length ↦ (2 / (H.length - 1 : ℝ)))).symm
    _ = (((H.length - 1) / 2 : ℕ) : ℝ) * (2 / (H.length - 1 : ℝ)) := by
          simp [Finset.sum_const, nsmul_eq_mul, antiholeAlternatingCliqueStartCount (H := H) j]
    _ = 1 := by
          rcases hodd.exists_bit1 with ⟨m, hm⟩
          have hlen_lower : 5 ≤ 2 * m + 1 := by
            simpa [hm] using H.length_ge_five
          have hm_pos : 0 < m := by
            omega
          have hm_ne : (m : ℝ) ≠ 0 := by
            exact_mod_cast Nat.ne_of_gt hm_pos
          rw [hm]
          norm_num
          field_simp [hm_ne]

/-- Helper for Exercise 7.19: the aggregated alternating-antihole clique coefficients equal the
indicator of `H.vertexFinset` when `H.length` is odd. -/
private lemma antiholeAlternatingCliqueMultiplier_coefficients
    (H : AntiholeSupport V)
    (hodd : Odd H.length) :
    (fun v ↦ ∑ K : Finset V,
      antiholeAlternatingCliqueMultiplier H K * (if v ∈ K then 1 else 0)) =
      stableSetIndicator H.vertexFinset := by
  classical
  funext v
  by_cases hv : v ∈ H.vertexFinset
  · rcases (AntiholeSupport.mem_vertexFinset_iff H).1 hv with ⟨j, rfl⟩
    calc
      ∑ K : Finset V,
          antiholeAlternatingCliqueMultiplier H K *
            (if H.verts j ∈ K then 1 else 0)
          = ∑ K : Finset V,
              (∑ i : Fin H.length,
                (if K = antiholeAlternatingClique H i
                  then (2 / (H.length - 1 : ℝ)) else 0) *
                  (if H.verts j ∈ K then 1 else 0)) := by
                simp [antiholeAlternatingCliqueMultiplier, Finset.mul_sum]
      _ = ∑ i : Fin H.length, ∑ K : Finset V,
            (if K = antiholeAlternatingClique H i
              then (2 / (H.length - 1 : ℝ)) else 0) *
              (if H.verts j ∈ K then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin H.length,
            if H.verts j ∈ antiholeAlternatingClique H i then
              (2 / (H.length - 1 : ℝ)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact antiholeAlternatingCliqueMultiplier_inner H i (H.verts j)
      _ = 1 := antiholeAlternatingCliqueCoefficientAtLabel (H := H) hodd j
      _ = stableSetIndicator H.vertexFinset (H.verts j) := by
            simp [stableSetIndicator, AntiholeSupport.mem_vertexFinset_iff]
  · have hzero :
      ∑ i : Fin H.length,
        (if v ∈ antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [not_mem_antiholeAlternatingClique_of_not_vertex (H := H) hv i]
    calc
      ∑ K : Finset V,
          antiholeAlternatingCliqueMultiplier H K * (if v ∈ K then 1 else 0)
          = ∑ K : Finset V,
              (∑ i : Fin H.length,
                (if K = antiholeAlternatingClique H i
                  then (2 / (H.length - 1 : ℝ)) else 0) *
                  (if v ∈ K then 1 else 0)) := by
                simp [antiholeAlternatingCliqueMultiplier, Finset.mul_sum]
      _ = ∑ i : Fin H.length, ∑ K : Finset V,
            (if K = antiholeAlternatingClique H i
              then (2 / (H.length - 1 : ℝ)) else 0) *
              (if v ∈ K then 1 else 0) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin H.length,
            if v ∈ antiholeAlternatingClique H i then
              (2 / (H.length - 1 : ℝ)) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact antiholeAlternatingCliqueMultiplier_inner H i v
      _ = 0 := hzero
      _ = stableSetIndicator H.vertexFinset v := by
            simp [stableSetIndicator, hv]

/-- Helper for Exercise 7.19: the total alternating-antihole multiplier is the constant
multiplier summed over all cyclic starts. -/
private lemma antiholeAlternatingCliqueMultiplier_sum
    (H : AntiholeSupport V) :
    ∑ K : Finset V, antiholeAlternatingCliqueMultiplier H K =
      ∑ i : Fin H.length, (2 / (H.length - 1 : ℝ)) := by
  calc
    ∑ K : Finset V, antiholeAlternatingCliqueMultiplier H K
        = ∑ K : Finset V,
            ∑ i : Fin H.length,
              if K = antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0 := by
              rfl
    _ = ∑ i : Fin H.length, ∑ K : Finset V,
          if K = antiholeAlternatingClique H i then (2 / (H.length - 1 : ℝ)) else 0 := by
            rw [Finset.sum_comm]
    _ = ∑ i : Fin H.length, (2 / (H.length - 1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp

/-- Exercise 7.19 (4). For an odd antihole support `H` contained in `G`, the antihole inequality
`∑_{v ∈ H.vertexFinset} x_v ≤ 2` is a Chvatal inequality for the clique relaxation `K(G)`. -/
theorem exercise_7_19_antihole_inequality_is_chvatal
    (H : AntiholeSupport V)
    (hH : H.IsContainedIn G)
    (hodd : Odd H.length) :
    IsCliqueRelaxationChvatalInequality
      G
      (stableSetIndicator H.vertexFinset)
      2 := by
  classical
  -- Route correction: the floor normalization is already isolated, so the proof now mirrors the
  -- web certificate and only needs the alternating-antihole clique family and its count formula.
  rw [isCliqueRelaxationChvatalInequality_iff]
  refine ⟨antiholeAlternatingCliqueMultiplier H, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The certificate uses only the nonnegative constant multiplier `2 / (H.length - 1)`.
    exact antiholeAlternatingCliqueMultiplier_nonneg H
  · -- Any nonzero multiplier comes from one alternating antihole clique, hence from a clique of
    -- `G`.
    exact antiholeAlternatingCliqueMultiplier_support (G := G) H hH
  · -- The slack vector is identically zero.
    intro v
    simp
  · -- Each coefficient of the support indicator is integral.
    intro v
    by_cases hv : v ∈ H.vertexFinset
    · exact ⟨1, by simp [stableSetIndicator, hv]⟩
    · exact ⟨0, by simp [stableSetIndicator, hv]⟩
  · -- The aggregated clique coefficients recover exactly the antihole-support indicator.
    ext v
    simpa using congrFun (antiholeAlternatingCliqueMultiplier_coefficients (H := H) hodd) v
  · -- The floored total multiplier is the antihole right-hand side `2`.
    rw [antiholeAlternatingCliqueMultiplier_sum]
    exact (antiholeCliqueMultiplier_floor H hodd).symm

/-- Exercise 7.19 (6). If `W` is a contained web support `W_n^k` in `G` and `n` is not divisible
by `k + 1`, then the web inequality on `W.vertexFinset` is a Chvatal inequality for the clique
relaxation `K(G)`. -/
theorem exercise_7_19_web_inequality_is_chvatal
    (W : WebSupport V)
    (hW : W.IsContainedIn G)
    (hndiv : ¬ (W.width + 1 ∣ W.length)) :
    IsCliqueRelaxationChvatalInequality
      G
      (stableSetIndicator W.vertexFinset)
      (web_inequality_rhs W) := by
  classical
  rw [isCliqueRelaxationChvatalInequality_iff]
  refine ⟨webForwardBlockMultiplier W, 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- The forward-block certificate uses only the nonnegative constant multiplier `1 / (k + 1)`.
    exact webForwardBlockMultiplier_nonneg (W := W)
  · -- Any nonzero multiplier comes from one of the forward blocks, hence from a clique of `G`.
    exact webForwardBlockMultiplier_support (G := G) W hW
  · -- The slack vector is identically zero.
    intro v
    simp
  · -- The support indicator has integral `0/1` coordinates.
    intro v
    by_cases hv : v ∈ W.vertexFinset
    · exact ⟨1, by simp [stableSetIndicator, hv]⟩
    · exact ⟨0, by simp [stableSetIndicator, hv]⟩
  · -- Summing the forward-block incidences recovers the support indicator of `W`.
    ext v
    simpa using congrFun (webForwardBlockMultiplier_coefficients (W := W)) v
  · -- The floored total multiplier is exactly the web right-hand side `⌊n / (k + 1)⌋`.
    symm
    rw [webForwardBlockMultiplier_sum]
    exact webBlockMultiplier_floor W

end ChvatalStatements

end Exercise_7_19

#print axioms exercise_7_19_clique_inequality_facet_defining_iff_maximal_clique
#print axioms exercise_7_19_odd_cycle_inequality_facet_defining_iff_chordless
#print axioms exercise_7_19_antihole_inequality_facet_defining
#print axioms exercise_7_19_odd_cycle_inequality_is_chvatal
#print axioms exercise_7_19_antihole_inequality_is_chvatal
#print axioms exercise_7_19_web_inequality_is_chvatal

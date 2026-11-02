import Mathlib

universe u v

section Definition_4_3_3_extra_2

variable {V : Type u} {A : Type v}

/-- The orientation in which an original arc is traversed in the residual network. -/
inductive ResidualArcOrientation
  | forward
  | backward
deriving DecidableEq, Repr

/-- A residual arc is an original arc together with the orientation in which the residual network
traverses it. This keeps the chapter's edge-indexed network owner, so parallel original arcs stay
distinguishable. -/
structure ResidualArc (A : Type v) where
  edge : A
  orientation : ResidualArcOrientation
deriving DecidableEq, Repr

/-- The residual tail of an oriented original arc. -/
def ResidualArc.tail (tail head : A → V) (a : ResidualArc A) : V :=
  match a.orientation with
  | .forward => tail a.edge
  | .backward => head a.edge

/-- The residual head of an oriented original arc. -/
def ResidualArc.head (tail head : A → V) (a : ResidualArc A) : V :=
  match a.orientation with
  | .forward => head a.edge
  | .backward => tail a.edge

/-- The residual capacity of an oriented original arc with respect to the current flow `x`. -/
def residual_arc_capacity (c x : A → ℝ) (a : ResidualArc A) : ℝ :=
  match a.orientation with
  | .forward => c a.edge - x a.edge
  | .backward => x a.edge

/-- A residual arc is active exactly when its residual capacity is positive. -/
def IsActiveResidualArc (c x : A → ℝ) (a : ResidualArc A) : Prop :=
  0 < residual_arc_capacity c x a

/-- The chapter's canonical residual-step relation on vertices: a step from `u` to `v` is realized
by an active oriented original arc whose residual tail is `u` and residual head is `v`. -/
def ResidualStep (tail head : A → V) (c x : A → ℝ) : V → V → Prop :=
  fun u v ↦
    ∃ a : ResidualArc A,
      IsActiveResidualArc c x a ∧
        ResidualArc.tail tail head a = u ∧
        ResidualArc.head tail head a = v

/-- A residual step is either a forward original arc with unused capacity or the reverse of an
original arc carrying positive flow. -/
theorem residualStep_iff
    (tail head : A → V) (c x : A → ℝ) (u v : V) :
    ResidualStep tail head c x u v ↔
      (∃ e : A, tail e = u ∧ head e = v ∧ x e < c e) ∨
        ∃ e : A, tail e = v ∧ head e = u ∧ 0 < x e := by
  constructor
  · rintro ⟨a, ha_active, ha_tail, ha_head⟩
    rcases a with ⟨e, ha_orientation⟩
    cases ha_orientation with
    | forward =>
        left
        refine ⟨e, ?_, ?_, ?_⟩
        · simpa [ResidualArc.tail] using ha_tail
        · simpa [ResidualArc.head] using ha_head
        · have hactive : 0 < c e - x e := by
            simpa [IsActiveResidualArc, residual_arc_capacity] using ha_active
          exact sub_pos.mp hactive
    | backward =>
        right
        refine ⟨e, ?_, ?_, ?_⟩
        · simpa [ResidualArc.head] using ha_head
        · simpa [ResidualArc.tail] using ha_tail
        · simpa [IsActiveResidualArc, residual_arc_capacity] using ha_active
  · rintro (⟨e, he_tail, he_head, he_active⟩ | ⟨e, he_tail, he_head, he_active⟩)
    · refine ⟨⟨e, .forward⟩, ?_, ?_, ?_⟩
      · simpa [IsActiveResidualArc, residual_arc_capacity] using sub_pos.mpr he_active
      · simpa [ResidualArc.tail] using he_tail
      · simpa [ResidualArc.head] using he_head
    · refine ⟨⟨e, .backward⟩, ?_, ?_, ?_⟩
      · simpa [IsActiveResidualArc, residual_arc_capacity] using he_active
      · simpa [ResidualArc.tail] using he_head
      · simpa [ResidualArc.head] using he_tail

/-- Definition 4.3.3-extra-2. The residual digraph of a network is the digraph on the same
vertices whose edges are the residual steps. -/
def residual_digraph (tail head : A → V) (c x : A → ℝ) : Digraph V where
  Adj := ResidualStep tail head c x

/-- Adjacency in the residual digraph is exactly the forward/backward residual-step condition. -/
theorem residual_digraph_adj_iff
    (tail head : A → V) (c x : A → ℝ) (u v : V) :
    (residual_digraph tail head c x).Adj u v ↔
      (∃ e : A, tail e = u ∧ head e = v ∧ x e < c e) ∨
        ∃ e : A, tail e = v ∧ head e = u ∧ 0 < x e := by
  simpa [residual_digraph] using residualStep_iff tail head c x u v

end Definition_4_3_3_extra_2

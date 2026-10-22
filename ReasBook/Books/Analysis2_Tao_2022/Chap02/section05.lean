/-
Authors: Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/Analysis2_Tao_2022/README.md (Contributors).
-/

import Mathlib

section Chap02
section Section05

universe u

/-- Definition 2.12: A topological space is a pair `(X, O)` consisting of a set `X` and a collection
`O` subset `2^X` such that (1) the empty set and `X` are in `O`, (2) finite intersections of members of
`O` are in `O`, and (3) arbitrary unions of members of `O` are in `O`; the members of `O` are
called open sets and `O` is called a topology on `X`. In Lean we bundle this as a type equipped with a
`TopologicalSpace` structure. -/
abbrev TopologicalSpacePair : Type (u + 1) :=
  Σ X : Type u, TopologicalSpace X

/-- Definition 2.13: A set `U ⊆ X` is a neighborhood of `x` in a topological space if `U` is open
and `x ∈ U`. -/
def IsNeighborhood {X : Type u} [TopologicalSpace X] (x : X) (U : Set X) : Prop :=
  IsOpen U ∧ x ∈ U

/-- Definition 2.14: [Topological convergence] Let `(X, 𝓕)` be a topological space, let `m ∈ ℤ`,
and let `(x^{(n)})_{n=m}^{∞}` be a sequence in `X`. For `x ∈ X`, the sequence converges to `x` iff
for every neighborhood `V` of `x` there exists an integer `N ≥ m` such that `x^{(n)} ∈ V` for all
integers `n ≥ N`. -/
def TopologicalConvergesFrom {X : Type u} [TopologicalSpace X] (m : ℤ) (xseq : ℤ → X) (x : X) :
    Prop :=
  ∀ V : Set X, IsNeighborhood x V → ∃ N ≥ m, ∀ n ≥ N, xseq n ∈ V

/-- Definition 2.15: [Interior point, exterior point, boundary point] Let `(X, 𝓕)` be a
topological space, let `E ⊆ X`, and let `x0 ∈ X`. (1) `x0` is an interior point of `E` iff there
exists a neighborhood `V` of `x0` with `V ⊆ E`. (2) `x0` is an exterior point of `E` iff there
exists a neighborhood `V` of `x0` with `V ∩ E = ∅`. (3) `x0` is a boundary point of `E` iff it is
neither interior nor exterior; equivalently, for every neighborhood `V` of `x0`, both `V ∩ E ≠ ∅`
and `V ∩ (X \ E) ≠ ∅`. -/
def IsInteriorPointTopological {X : Type u} [TopologicalSpace X] (E : Set X) (x0 : X) : Prop :=
  ∃ V : Set X, IsNeighborhood x0 V ∧ V ⊆ E

/-- A point is an exterior point of `E` if some neighborhood of it misses `E`. -/
def IsExteriorPointTopological {X : Type u} [TopologicalSpace X] (E : Set X) (x0 : X) : Prop :=
  ∃ V : Set X, IsNeighborhood x0 V ∧ V ∩ E = ∅

/-- A point is a boundary point of `E` if it is neither interior nor exterior. -/
def IsBoundaryPointTopological {X : Type u} [TopologicalSpace X] (E : Set X) (x0 : X) : Prop :=
  ¬ IsInteriorPointTopological E x0 ∧ ¬ IsExteriorPointTopological E x0

/-- A point is adherent to `E` if every neighborhood containing an open neighborhood of it meets `E`.
-/
def IsAdherentPointTopological {X : Type u} [TopologicalSpace X] (E : Set X) (x0 : X) : Prop :=
  ∀ V : Set X, (∃ U : Set X, IsNeighborhood x0 U ∧ U ⊆ V) → (V ∩ E).Nonempty

/-- Definition 2.16 (Closure point): Let `(X, 𝓕)` be a topological space and `E ⊆ X`. (1) A point
`x0 ∈ X` is an adherent point of `E` iff for every neighborhood `V` of `x0` (i.e., `V` contains an
open set containing `x0`), one has `V ∩ E ≠ ∅`. (2) The closure `\overline{E}` is the set of all
adherent points of `E`: `\overline{E} = {x ∈ X : for every neighborhood V of x, V ∩ E ≠ ∅}`. -/
def closureSetTopological {X : Type u} [TopologicalSpace X] (E : Set X) : Set X :=
  {x | IsAdherentPointTopological E x}

/-- Definition 2.17: Let `(X, 𝓕)` be a topological space and `K ⊆ X`. The set `K` is closed iff
its complement `X \ K` is open (i.e. `X \ K ∈ 𝓕`). -/
abbrev IsClosedTopological {X : Type u} [TopologicalSpace X] (K : Set X) : Prop :=
  IsClosed K

/-- Definition 2.18: [Relative topology] Let `(X, 𝓕)` be a topological space and `Y ⊆ X`. Define
`𝓕_Y := {V ∩ Y : V ∈ 𝓕}`; this collection is the relative (subspace) topology on `Y`, and the
pair `(Y, 𝓕_Y)` is a topological subspace of `(X, 𝓕)`. -/
def relativeTopology {X : Type u} [TopologicalSpace X] (Y : Set X) : Set (Set X) :=
  {U : Set X | ∃ V : Set X, IsOpen V ∧ U = V ∩ Y}

/-- Definition 2.19: (Continuous functions) Let `(X, 𝓕_X)` and `(Y, 𝓕_Y)` be topological spaces
and let `f : X → Y`. For `x0 ∈ X`, the function `f` is continuous at `x0` iff for every
neighborhood `V` of `f x0` there exists a neighborhood `U` of `x0` such that `f '' U ⊆ V`.
The function `f` is continuous iff it is continuous at every point `x ∈ X`. -/
def IsContinuousAtTopological {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (x0 : X) : Prop :=
  ∀ V : Set Y, IsNeighborhood (f x0) V → ∃ U : Set X, IsNeighborhood x0 U ∧ f '' U ⊆ V

/-- A function is continuous if it is continuous at every point. -/
def IsContinuousTopological {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  ∀ x : X, IsContinuousAtTopological f x

/-- Definition 2.20: (1) A topological space is compact if every open cover has a finite subcover.
(2) A subset `Y ⊆ X` is compact if the subspace topology on `Y` is compact; in Lean we use
`IsCompact Y`, and the space is compact iff `IsCompact (Set.univ : Set X)`. -/
abbrev IsCompactTopological {X : Type u} [TopologicalSpace X] (Y : Set X) : Prop :=
  IsCompact Y

/-- A topological space is compact if its underlying set is compact. -/
abbrev IsCompactSpaceTopological {X : Type u} [TopologicalSpace X] : Prop :=
  IsCompactTopological (Set.univ : Set X)

/-- Definition 2.22 (Hausdorff topological space): A topological space is Hausdorff if for any
distinct points `x, y` there exist neighborhoods `V` of `x` and `W` of `y` with `V ∩ W = ∅`. -/
abbrev IsHausdorffTopological (X : Type u) [TopologicalSpace X] : Prop :=
  T2Space X

/-- Definition 2.23: [Order topology] Let `(X, ≤)` be a totally ordered set. A set `V ⊆ X` is open
if for every `x ∈ V` there exists a set `I` with `x ∈ I ⊆ V`, where `I` is an interval
`{y : X | a < y ∧ y < b}`, a ray `{y : X | a < y}` or `{y : X | y < b}`, or the whole space `X`;
the collection of such open sets defines the order topology on `X`. -/
abbrev orderTopology (X : Type u) [LinearOrder X] : TopologicalSpace X :=
  Preorder.topology X

/-- Definition 2.24 (Cofinite topology): Let `X` be a set and define
`𝓕 := {E ⊆ X | E = ∅ or X \ E` is finite}. The pair `(X, 𝓕)` is called the cofinite topology on
`X`. In Lean this is the `TopologicalSpace` structure induced by the `CofiniteTopology` type
synonym. -/
abbrev cofiniteTopology (X : Type u) : TopologicalSpace X :=
  TopologicalSpace.cofinite

/-- A set is cocountable-open if it is empty or its complement is countable. -/
def IsCocountableOpen (X : Type u) (E : Set X) : Prop :=
  E = ∅ ∨ (Set.univ \ E).Countable

/-- The whole space is cocountable-open. -/
lemma cocountable_isOpen_univ (X : Type u) : IsCocountableOpen X (Set.univ : Set X) := by
  right
  simpa using (Set.countable_empty : (∅ : Set X).Countable)

/-- Intersections of cocountable-open sets are cocountable-open. -/
lemma cocountable_isOpen_inter (X : Type u) (s t : Set X) :
    IsCocountableOpen X s → IsCocountableOpen X t → IsCocountableOpen X (s ∩ t) := by
  intro hs ht
  rcases hs with rfl | hsCount
  · left
    simp
  · rcases ht with rfl | htCount
    · left
      simp
    · right
      simpa [Set.diff_inter] using hsCount.union htCount

/-- Arbitrary unions of cocountable-open sets are cocountable-open. -/
lemma cocountable_isOpen_sUnion (X : Type u) (S : Set (Set X)) :
    (∀ t ∈ S, IsCocountableOpen X t) → IsCocountableOpen X (⋃₀ S) := by
  intro hS
  by_cases hUnion : (⋃₀ S : Set X) = ∅
  · left
    exact hUnion
  · right
    have hUnionNonempty : (⋃₀ S : Set X).Nonempty := by
      by_contra hNonempty
      apply hUnion
      refine Set.eq_empty_iff_forall_notMem.mpr ?_
      intro x hx
      exact hNonempty ⟨x, hx⟩
    rcases hUnionNonempty with ⟨x, hxUnion⟩
    rcases Set.mem_sUnion.mp hxUnion with ⟨t, htS, hxT⟩
    have htComplCount : (Set.univ \ t).Countable := by
      rcases hS t htS with htEmpty | htCount
      · exfalso
        rw [htEmpty] at hxT
        exact hxT
      · exact htCount
    have hsubset : Set.univ \ ⋃₀ S ⊆ Set.univ \ t := by
      intro y hy
      rcases hy with ⟨hyUniv, hyNotUnion⟩
      refine ⟨hyUniv, ?_⟩
      intro hyMemT
      exact hyNotUnion (Set.mem_sUnion.mpr ⟨t, htS, hyMemT⟩)
    exact Set.Countable.mono hsubset htComplCount

/-- Definition 2.25 (Cocountable topology): Let `X` be a set. Define
`𝓕 := {E ⊆ X | E = ∅ or X \ E is at most countable}`. The pair `(X, 𝓕)` is called the
cocountable topology on `X`. -/
@[reducible] def cocountableTopology (X : Type u) : TopologicalSpace X :=
  { IsOpen := IsCocountableOpen X
    isOpen_univ := cocountable_isOpen_univ X
    isOpen_inter := cocountable_isOpen_inter X
    isOpen_sUnion := cocountable_isOpen_sUnion X }

/-- Proposition 2.23: In a metric space, the open ball `Metric.ball x r` with `r > 0` is a
neighborhood of `x`. -/
theorem metric_ball_isNeighborhood {X : Type u} [MetricSpace X] (x : X) {r : ℝ} (hr : 0 < r) :
    IsNeighborhood x (Metric.ball x r) := by
  unfold IsNeighborhood
  constructor
  · simpa using (Metric.isOpen_ball : IsOpen (Metric.ball x r))
  · simpa using (Metric.mem_ball_self (x := x) hr)

/-- Proposition 2.24: Let `(x_n)` be a sequence in `ℝ`, viewed in the extended real line `EReal`.
Then `x_n → +∞` iff `liminf_{n→∞} x_n = +∞`. Similarly, `x_n → -∞` iff
`limsup_{n→∞} x_n = -∞`. -/
theorem tendsto_ereal_top_iff_liminf_eq_top_and_tendsto_ereal_bot_iff_limsup_eq_bot
    (x : ℕ → ℝ) :
    (Filter.Tendsto (fun n => (x n : EReal)) Filter.atTop (nhds (⊤ : EReal)) ↔
        Filter.liminf (fun n => (x n : EReal)) Filter.atTop = (⊤ : EReal)) ∧
      (Filter.Tendsto (fun n => (x n : EReal)) Filter.atTop (nhds (⊥ : EReal)) ↔
        Filter.limsup (fun n => (x n : EReal)) Filter.atTop = (⊥ : EReal)) := by
  constructor
  · constructor
    · intro h
      simpa using
        (Filter.Tendsto.liminf_eq (f := Filter.atTop) (u := fun n => (x n : EReal))
          (a := (⊤ : EReal)) h)
    · intro h
      refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
      · simpa [h]
      · exact le_top
  · constructor
    · intro h
      simpa using
        (Filter.Tendsto.limsup_eq (f := Filter.atTop) (u := fun n => (x n : EReal))
          (a := (⊥ : EReal)) h)
    · intro h
      refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
      · exact bot_le
      · simpa [h]

/-- Proposition 2.25: Let `X` be a set and define `𝓕 := {∅, X}`. Then `(X, 𝓕)` is a topology on
`X`, i.e. there is a topological structure whose open sets are exactly `∅` and `Set.univ`. -/
theorem exists_topology_only_empty_univ (X : Type u) :
    ∃ T : TopologicalSpace X, ∀ U : Set X, @IsOpen X T U ↔ U = ∅ ∨ U = Set.univ := by
  refine ⟨⊤, ?_⟩
  intro U
  simpa using (TopologicalSpace.isOpen_top_iff (U := U))

/-- Definition 2.26: [First countable topological space] A topological space `(X, F)` is first
countable if for every `x in X` there exists a countable collection of neighborhoods
`V_1, V_2, ...` of `x` such that every neighborhood of `x` contains at least one `V_n`. In Lean
this is the predicate `FirstCountableTopology`. -/
abbrev IsFirstCountableTopological (X : Type u) [TopologicalSpace X] : Prop :=
  FirstCountableTopology X

end Section05
end Chap02

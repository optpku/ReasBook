/-
Authors: Zichen Wang, Wanli Ma, Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap01
section Section02

/-- Definition 1.10 (Balls): Let `(X,d)` be a metric space, let `x0 ∈ X`, and let `r > 0`.
The (open) ball in `X` centered at `x0` with radius `r` is the set
`B_{(X,d)}(x0,r) = {x ∈ X : d(x,x0) < r}`. -/
abbrev taoOpenBall (X : Type*) [MetricSpace X] (x0 : X) (r : Real) : Set X :=
  Metric.ball x0 r

/-- Definition 1.11 (Interior/exterior/boundary points): Let `(X,d)` be a metric space and `E ⊆ X`.
(1) `x ∈ X` is an interior point of `E` iff there exists `r > 0` with `B(x,r) ⊆ E`.
(2) `x ∈ X` is an exterior point of `E` iff there exists `r > 0` with `B(x,r) ⊆ Eᶜ`.
(3) `x ∈ X` is a boundary point of `E` iff for every `r > 0`, both `B(x,r) ∩ E ≠ ∅`
and `B(x,r) ∩ Eᶜ ≠ ∅`. -/
def IsInteriorPoint {X : Type*} [MetricSpace X] (E : Set X) (x : X) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ E

/-- A point is an exterior point of `E` if some positive ball around it is contained in `Eᶜ`. -/
def IsExteriorPoint {X : Type*} [MetricSpace X] (E : Set X) (x : X) : Prop :=
  ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ Eᶜ

/-- A point is a boundary point of `E` if every positive ball meets both `E` and `Eᶜ`. -/
def IsBoundaryPoint {X : Type*} [MetricSpace X] (E : Set X) (x : X) : Prop :=
  ∀ r : ℝ, 0 < r →
    ((Metric.ball x r) ∩ E).Nonempty ∧ ((Metric.ball x r) ∩ Eᶜ).Nonempty

/-- Interior points defined via balls coincide with membership in `interior`. -/
lemma isInteriorPoint_iff_mem_interior {X : Type*} [MetricSpace X] (E : Set X) (x : X) :
    IsInteriorPoint E x ↔ x ∈ interior E :=
by
  rw [mem_interior_iff_mem_nhds]
  simpa [IsInteriorPoint] using
    (Metric.mem_nhds_iff (x := x) (s := E)).symm

/-- Exterior points defined via balls coincide with membership in `interior` of the complement. -/
lemma isExteriorPoint_iff_mem_interior_compl {X : Type*} [MetricSpace X] (E : Set X) (x : X) :
    IsExteriorPoint E x ↔ x ∈ interior (Eᶜ) :=
by
  simpa [IsExteriorPoint, IsInteriorPoint] using
    (isInteriorPoint_iff_mem_interior (E := Eᶜ) (x := x))

/-- Characterize closure via nonempty intersections of all positive balls. -/
lemma mem_closure_iff_forall_ball_inter_nonempty {X : Type*} [MetricSpace X] (s : Set X) (x : X) :
    x ∈ closure s ↔ ∀ r : ℝ, 0 < r → ((Metric.ball x r) ∩ s).Nonempty :=
by
  constructor
  · intro hx r hr
    rcases (Metric.mem_closure_iff.mp hx) r hr with ⟨y, hy_s, hy_dist⟩
    have hy_ball : y ∈ Metric.ball x r := Metric.mem_ball'.2 hy_dist
    refine ⟨y, ?_⟩
    exact ⟨hy_ball, hy_s⟩
  · intro hx
    apply Metric.mem_closure_iff.mpr
    intro r hr
    rcases hx r hr with ⟨y, hy⟩
    rcases hy with ⟨hy_ball, hy_s⟩
    have hy_dist : dist x y < r := Metric.mem_ball'.1 hy_ball
    exact ⟨y, hy_s, hy_dist⟩

/-- Boundary points are exactly those in the closures of the set and its complement. -/
lemma isBoundaryPoint_iff_mem_closure_inter_closure_compl {X : Type*} [MetricSpace X]
    (E : Set X) (x : X) :
    IsBoundaryPoint E x ↔ x ∈ closure E ∩ closure (Eᶜ) :=
by
  constructor
  · intro hx
    have hxE : x ∈ closure E := by
      apply (mem_closure_iff_forall_ball_inter_nonempty (s := E) (x := x)).2
      intro r hr
      exact (hx r hr).1
    have hxEc : x ∈ closure (Eᶜ) := by
      apply (mem_closure_iff_forall_ball_inter_nonempty (s := Eᶜ) (x := x)).2
      intro r hr
      exact (hx r hr).2
    exact ⟨hxE, hxEc⟩
  · intro hx
    rcases hx with ⟨hxE, hxEc⟩
    intro r hr
    have hE : ((Metric.ball x r) ∩ E).Nonempty :=
      (mem_closure_iff_forall_ball_inter_nonempty (s := E) (x := x)).1 hxE r hr
    have hEc : ((Metric.ball x r) ∩ Eᶜ).Nonempty :=
      (mem_closure_iff_forall_ball_inter_nonempty (s := Eᶜ) (x := x)).1 hxEc r hr
    exact ⟨hE, hEc⟩

/-- Boundary points defined via balls coincide with membership in `frontier`. -/
lemma isBoundaryPoint_iff_mem_frontier {X : Type*} [MetricSpace X] (E : Set X) (x : X) :
    IsBoundaryPoint E x ↔ x ∈ frontier E :=
by
  simpa [frontier_eq_closure_inter_closure] using
    (isBoundaryPoint_iff_mem_closure_inter_closure_compl (E := E) (x := x))

/-- Definition 1.12 (Interior, exterior, boundary): Let `(X,d)` be a metric space and `E ⊆ X`.
(1) `x ∈ X` is an interior point of `E` iff there exists `r > 0` with `B(x,r) ⊆ E`.
(2) `x ∈ X` is an exterior point of `E` iff there exists `r > 0` with `B(x,r) ∩ E = ∅`.
(3) `x ∈ X` is a boundary point of `E` iff it is neither interior nor exterior.
The interior (resp. exterior, boundary) of `E` is the set of all interior (resp. exterior, boundary) points. -/
def interiorSet {X : Type*} [MetricSpace X] (E : Set X) : Set X :=
  {x | IsInteriorPoint E x}

/-- The exterior set of `E` as the set of exterior points. -/
def exteriorSet {X : Type*} [MetricSpace X] (E : Set X) : Set X :=
  {x | IsExteriorPoint E x}

/-- The boundary set of `E` as the set of points that are neither interior nor exterior. -/
def boundarySet {X : Type*} [MetricSpace X] (E : Set X) : Set X :=
  {x | ¬ IsInteriorPoint E x ∧ ¬ IsExteriorPoint E x}

/-- The book's interior set agrees with `interior`. -/
lemma interiorSet_eq_interior {X : Type*} [MetricSpace X] (E : Set X) :
    interiorSet E = interior E :=
by
  ext x
  simpa [interiorSet] using (isInteriorPoint_iff_mem_interior (E := E) (x := x))

/-- The book's exterior set agrees with `interior (Eᶜ)`. -/
lemma exteriorSet_eq_interior_compl {X : Type*} [MetricSpace X] (E : Set X) :
    exteriorSet E = interior (Eᶜ) :=
by
  ext x
  simpa [exteriorSet] using
    (isExteriorPoint_iff_mem_interior_compl (E := E) (x := x))

/-- The book's boundary set agrees with `frontier`. -/
lemma boundarySet_eq_frontier {X : Type*} [MetricSpace X] (E : Set X) :
    boundarySet E = frontier E :=
by
  ext x
  simp [boundarySet, frontier_eq_inter_compl_interior, isInteriorPoint_iff_mem_interior,
    isExteriorPoint_iff_mem_interior_compl]

/-- Proposition 1.11: Let `(X,d)` be a metric space and `E ⊆ X`. Define
`int(E) = {x ∈ X : ∃ r > 0, B(x,r) ⊆ E}`, `ext(E) = int(X \ E)`, and
`∂E = X \ (int(E) ∪ ext(E))`, where `B(x,r) = {y ∈ X : d(x,y) < r}`. Then:
(1) If `x0 ∈ int(E)`, then `x0 ∈ E`.
(2) If `x0 ∈ ext(E)`, then `x0 ∉ E`.
(3) `int(E) ∩ ext(E) = ∅`.
(4) If `x0 ∈ ∂E`, then it is possible that `x0 ∈ E` and it is possible that `x0 ∉ E`. -/
lemma proposition_1_11 {X : Type*} [MetricSpace X] (E : Set X) :
    (∀ x0, x0 ∈ interiorSet E → x0 ∈ E) ∧
    (∀ x0, x0 ∈ exteriorSet E → x0 ∉ E) ∧
    (interiorSet E ∩ exteriorSet E = (∅ : Set X)) ∧
    (∀ x0, x0 ∈ boundarySet E → (x0 ∈ E ∨ x0 ∉ E)) :=
by
  refine And.intro ?h1 ?hrest
  · intro x0 hx0
    rcases hx0 with ⟨r, hrpos, hsubset⟩
    have hxball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hrpos
    exact hsubset hxball
  · refine And.intro ?h2 ?hrest2
    · intro x0 hx0
      rcases hx0 with ⟨r, hrpos, hsubset⟩
      have hxball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hrpos
      have hxcompl : x0 ∈ Eᶜ := hsubset hxball
      simpa using hxcompl
    · refine And.intro ?h3 ?h4
      · ext x
        constructor
        · intro hx
          rcases hx with ⟨hxI, hxE⟩
          rcases hxI with ⟨rI, hrIpos, hI⟩
          rcases hxE with ⟨rE, hrEpos, hE⟩
          have hxballI : x ∈ Metric.ball x rI := Metric.mem_ball_self hrIpos
          have hxballE : x ∈ Metric.ball x rE := Metric.mem_ball_self hrEpos
          have hxmem : x ∈ E := hI hxballI
          have hxnot : x ∈ Eᶜ := hE hxballE
          have hxnot' : x ∉ E := by
            simpa using hxnot
          exact (hxnot' hxmem).elim
        · intro hx
          cases hx
      · intro x0 hx0
        classical
        exact Classical.em (x0 ∈ E)

/-- If a point lies in the interior set, then it lies in the set. -/
lemma mem_of_mem_interiorSet {X : Type*} [MetricSpace X] {E : Set X} {x0 : X} :
    x0 ∈ interiorSet E → x0 ∈ E :=
by
  intro hx0
  rcases hx0 with ⟨r, hrpos, hsubset⟩
  have hxball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hrpos
  exact hsubset hxball

/-- If a point lies in the exterior set, then it is not in the set. -/
lemma mem_compl_of_mem_exteriorSet {X : Type*} [MetricSpace X] {E : Set X} {x0 : X} :
    x0 ∈ exteriorSet E → x0 ∉ E :=
by
  intro hx0
  rcases hx0 with ⟨r, hrpos, hsubset⟩
  have hxball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hrpos
  have hxcompl : x0 ∈ Eᶜ := hsubset hxball
  simpa using hxcompl

/-- The interior and exterior sets are disjoint. -/
lemma interiorSet_inter_exteriorSet_eq_empty {X : Type*} [MetricSpace X] (E : Set X) :
    interiorSet E ∩ exteriorSet E = (∅ : Set X) :=
by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxI, hxE⟩
    have hxmem : x ∈ E := mem_of_mem_interiorSet (x0 := x) hxI
    have hxnot : x ∉ E := mem_compl_of_mem_exteriorSet (x0 := x) hxE
    exact (hxnot hxmem).elim
  · intro hx
    cases hx

/-- A boundary point may or may not lie in the set. -/
lemma mem_or_not_mem_of_mem_boundarySet {X : Type*} [MetricSpace X] {E : Set X} {x0 : X} :
    x0 ∈ boundarySet E → (x0 ∈ E ∨ x0 ∉ E) :=
by
  intro _
  classical
  exact Classical.em (x0 ∈ E)

/-- Helper for Proposition 1.12: `1 < 2` in `ℝ`. -/
lemma helperForProposition_1_12_one_lt_two : (1 : ℝ) < 2 :=
by
  norm_num

/-- Helper for Proposition 1.12: interior of `Ico` is `Ioo`. -/
lemma helperForProposition_1_12_interior_Ico :
    interior (Set.Ico (1 : ℝ) 2) = Set.Ioo (1 : ℝ) 2 :=
by
  exact interior_Ico (a := (1 : ℝ)) (b := 2)

/-- Helper for Proposition 1.12: interior of the complement of `Ico`. -/
lemma helperForProposition_1_12_interior_compl_Ico :
    interior ((Set.Ico (1 : ℝ) 2)ᶜ) = Set.Iio (1 : ℝ) ∪ Set.Ioi (2 : ℝ) :=
by
  have hne : (1 : ℝ) ≠ 2 := ne_of_lt helperForProposition_1_12_one_lt_two
  ext x
  simp [interior_compl, closure_Ico hne, Set.mem_Icc]
  by_cases h1 : x < (1 : ℝ)
  · have h1' : ¬ (1 : ℝ) ≤ x := not_le_of_gt h1
    constructor
    · intro _
      exact Or.inl h1
    · intro _ hle
      exact (h1' hle).elim
  · have h1' : (1 : ℝ) ≤ x := le_of_not_gt h1
    constructor
    · intro hx
      exact Or.inr (hx h1')
    · intro hx _
      cases hx with
      | inl hlt => exact (h1 hlt).elim
      | inr hgt => exact hgt

/-- Helper for Proposition 1.12: frontier of `Ico` is `{1,2}`. -/
lemma helperForProposition_1_12_frontier_Ico :
    frontier (Set.Ico (1 : ℝ) 2) = ({1, 2} : Set ℝ) :=
by
  exact frontier_Ico (a := (1 : ℝ)) (b := 2) helperForProposition_1_12_one_lt_two

/-- Proposition 1.12: Let `E = [1,2) ⊆ ℝ` with the standard metric. Then
`interior E = (1,2)`, `interior (Eᶜ) = (-∞,1) ∪ (2,∞)`, and `frontier E = {1,2}`.
In particular, `1 ∈ E ∩ frontier E` and `2 ∈ frontier E \ E`. -/
lemma real_Ico_interior_exterior_boundary :
    let E : Set ℝ := Set.Ico (1 : ℝ) 2
    ; interior E = Set.Ioo (1 : ℝ) 2 ∧
      interior (Eᶜ) = Set.Iio (1 : ℝ) ∪ Set.Ioi (2 : ℝ) ∧
      frontier E = ({1, 2} : Set ℝ) ∧
      (1 : ℝ) ∈ E ∩ frontier E ∧
      (2 : ℝ) ∈ frontier E \ E :=
by
  classical
  dsimp
  constructor
  · exact helperForProposition_1_12_interior_Ico
  · constructor
    · exact helperForProposition_1_12_interior_compl_Ico
    · constructor
      · exact helperForProposition_1_12_frontier_Ico
      · constructor
        · rw [helperForProposition_1_12_frontier_Ico]
          simp
        · rw [helperForProposition_1_12_frontier_Ico]
          simp

/-- Helper for Proposition 1.13: a singleton contains a positive-radius ball. -/
lemma helperForProposition_1_13_exists_ball_subset_singleton
    {X : Type*} [MetricSpace X] [DiscreteTopology X] (x : X) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ ({x} : Set X) :=
by
  have hopen : IsOpen ({x} : Set X) := isOpen_discrete _
  have hopen' :
      ∀ y ∈ ({x} : Set X), ∃ r > 0, Metric.ball y r ⊆ ({x} : Set X) :=
    (Metric.isOpen_iff).1 hopen
  have hxmem : x ∈ ({x} : Set X) := by
    simp
  exact hopen' x hxmem

/-- Helper for Proposition 1.13: points of `E` are interior points in the discrete topology. -/
lemma helperForProposition_1_13_mem_interiorSet_of_mem
    {X : Type*} [MetricSpace X] [DiscreteTopology X] {E : Set X} {x : X} :
    x ∈ E → x ∈ interiorSet E :=
by
  intro hxE
  rcases helperForProposition_1_13_exists_ball_subset_singleton (X := X) x with
    ⟨r, hrpos, hball⟩
  refine ⟨r, hrpos, ?_⟩
  have hsubset : ({x} : Set X) ⊆ E := (Set.singleton_subset_iff).2 hxE
  intro y hy
  exact hsubset (hball hy)

/-- Helper for Proposition 1.13: points of `Eᶜ` are exterior points in the discrete topology. -/
lemma helperForProposition_1_13_mem_exteriorSet_of_mem_compl
    {X : Type*} [MetricSpace X] [DiscreteTopology X] {E : Set X} {x : X} :
    x ∈ Eᶜ → x ∈ exteriorSet E :=
by
  intro hxE
  rcases helperForProposition_1_13_exists_ball_subset_singleton (X := X) x with
    ⟨r, hrpos, hball⟩
  refine ⟨r, hrpos, ?_⟩
  have hsubset : ({x} : Set X) ⊆ Eᶜ := (Set.singleton_subset_iff).2 hxE
  intro y hy
  exact hsubset (hball hy)

/-- Helper for Proposition 1.13: the boundary set is empty in the discrete topology. -/
lemma helperForProposition_1_13_boundarySet_eq_empty
    {X : Type*} [MetricSpace X] [DiscreteTopology X] (E : Set X) :
    boundarySet E = (∅ : Set X) :=
by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxI, hxE⟩
    classical
    by_cases hxmem : x ∈ E
    · have hxI' : IsInteriorPoint E x := by
        have hxint : x ∈ interiorSet E :=
          helperForProposition_1_13_mem_interiorSet_of_mem (E := E) (x := x) hxmem
        simpa [interiorSet] using hxint
      exact (hxI hxI').elim
    · have hxmem' : x ∈ Eᶜ := by
        simpa using hxmem
      have hxE' : IsExteriorPoint E x := by
        have hxext : x ∈ exteriorSet E :=
          helperForProposition_1_13_mem_exteriorSet_of_mem_compl (E := E) (x := x) hxmem'
        simpa [exteriorSet] using hxext
      exact (hxE hxE').elim
  · intro hx
    cases hx

/-- Proposition 1.13: Let `X` be a set equipped with the discrete metric `d_disc` with
`d_disc(x,y)=0` if `x=y` and `d_disc(x,y)=1` if `x≠y`. For every `E ⊆ X`,
`int(E)=E`, `ext(E)=X \ E`, and `∂E=∅`. -/
lemma proposition_1_13 {X : Type*} [MetricSpace X] [DiscreteTopology X] (E : Set X) :
    interiorSet E = E ∧ exteriorSet E = Eᶜ ∧ boundarySet E = (∅ : Set X) :=
by
  constructor
  · ext x
    constructor
    · intro hx
      exact mem_of_mem_interiorSet (x0 := x) hx
    · intro hx
      exact helperForProposition_1_13_mem_interiorSet_of_mem (E := E) (x := x) hx
  · constructor
    · ext x
      constructor
      · intro hx
        have hxnot : x ∉ E := mem_compl_of_mem_exteriorSet (x0 := x) hx
        simpa using hxnot
      · intro hx
        exact helperForProposition_1_13_mem_exteriorSet_of_mem_compl (E := E) (x := x) hx
    · exact helperForProposition_1_13_boundarySet_eq_empty (E := E)

/-- Definition 1.13 (Closure): Let `(X,d)` be a metric space and `E ⊆ X`.
A point `x ∈ X` is an adherent point of `E` iff for every `r > 0`,
`B(x,r) ∩ E ≠ ∅`, where `B(x,r) = {y ∈ X : d(x,y) < r}`.
The closure `\overline{E}` is the set of all adherent points:
`\overline{E} = {x ∈ X : ∀ r > 0, B(x,r) ∩ E ≠ ∅}`. -/
def closureSet {X : Type*} [MetricSpace X] (E : Set X) : Set X :=
  {x | ∀ r : ℝ, 0 < r → (Metric.ball x r ∩ E).Nonempty}

/-- A point is adherent to `E` if every positive ball around it meets `E`. -/
def IsAdherentPoint {X : Type*} [MetricSpace X] (E : Set X) (x : X) : Prop :=
  ∀ r : ℝ, 0 < r → (Metric.ball x r ∩ E).Nonempty

/-- Adherent points coincide with membership in `closure`. -/
lemma isAdherentPoint_iff_mem_closure {X : Type*} [MetricSpace X] (E : Set X) (x : X) :
    IsAdherentPoint E x ↔ x ∈ closure E :=
by
  simpa [IsAdherentPoint] using
    (mem_closure_iff_forall_ball_inter_nonempty (s := E) (x := x)).symm

/-- The closure of `E` as the set of adherent points. -/
lemma closureSet_eq_setOf_isAdherentPoint {X : Type*} [MetricSpace X] (E : Set X) :
    closureSet E = {x | IsAdherentPoint E x} :=
by
  rfl

/-- The book's closure set agrees with `closure`. -/
lemma closureSet_eq_closure {X : Type*} [MetricSpace X] (E : Set X) :
    closureSet E = closure E :=
by
  ext x
  constructor
  · intro hx
    have hx' : IsAdherentPoint E x := by
      simpa [closureSet, IsAdherentPoint] using hx
    exact (isAdherentPoint_iff_mem_closure (E := E) (x := x)).1 hx'
  · intro hx
    have hx' : IsAdherentPoint E x :=
      (isAdherentPoint_iff_mem_closure (E := E) (x := x)).2 hx
    simpa [closureSet, IsAdherentPoint] using hx'

/-- Helper for Proposition 1.14: adherent points coincide with closure membership. -/
lemma helperForProposition_1_14_isAdherentPoint_iff_mem_closure
    {X : Type*} [MetricSpace X] (E : Set X) (x0 : X) :
    IsAdherentPoint E x0 ↔ x0 ∈ closure E := by
  constructor
  · intro hAd
    refine (Metric.mem_closure_iff).2 ?_
    intro ε hε
    have hnon : (Metric.ball x0 ε ∩ E).Nonempty := hAd ε hε
    rcases hnon with ⟨y, hy⟩
    have hyball : y ∈ Metric.ball x0 ε := hy.1
    have hyE : y ∈ E := hy.2
    have hdist : dist x0 y < ε := by
      have hdist' : dist y x0 < ε := (Metric.mem_ball).1 hyball
      simpa [dist_comm] using hdist'
    exact ⟨y, hyE, hdist⟩
  · intro hxcl
    intro ε hε
    have h := (Metric.mem_closure_iff).1 hxcl ε hε
    rcases h with ⟨y, hyE, hdist⟩
    have hyball : y ∈ Metric.ball x0 ε := by
      have hdist' : dist y x0 < ε := by
        simpa [dist_comm] using hdist
      exact (Metric.mem_ball).2 hdist'
    refine ⟨y, ?_⟩
    exact ⟨hyball, hyE⟩

/-- Helper for Proposition 1.14: adherent points are interior or boundary points. -/
lemma helperForProposition_1_14_adherent_iff_interior_or_boundary
    {X : Type*} [MetricSpace X] (E : Set X) (x0 : X) :
    IsAdherentPoint E x0 ↔ IsInteriorPoint E x0 ∨ IsBoundaryPoint E x0 := by
  constructor
  · intro hAd
    classical
    by_cases hI : IsInteriorPoint E x0
    · exact Or.inl hI
    · right
      intro r hrpos
      have hE : (Metric.ball x0 r ∩ E).Nonempty := hAd r hrpos
      have hnot : ¬ Metric.ball x0 r ⊆ E := by
        intro hsubset
        apply hI
        exact ⟨r, hrpos, hsubset⟩
      rcases Set.not_subset.mp hnot with ⟨y, hyball, hyE⟩
      have hyc : y ∈ Eᶜ := by
        simpa using hyE
      have hEc : (Metric.ball x0 r ∩ Eᶜ).Nonempty := by
        refine ⟨y, ?_⟩
        exact ⟨hyball, hyc⟩
      exact ⟨hE, hEc⟩
  · intro h
    intro r hrpos
    cases h with
    | inl hI =>
        rcases hI with ⟨r0, hr0pos, hsubset⟩
        have hxE : x0 ∈ E := hsubset (Metric.mem_ball_self hr0pos)
        have hxball : x0 ∈ Metric.ball x0 r := Metric.mem_ball_self hrpos
        refine ⟨x0, ?_⟩
        exact ⟨hxball, hxE⟩
    | inr hB =>
        exact (hB r hrpos).1

/-- Helper for Proposition 1.14: adherent points admit convergent sequences from the set. -/
lemma helperForProposition_1_14_adherent_iff_exists_seq_tendsto
    {X : Type*} [MetricSpace X] (E : Set X) (x0 : X) :
    IsAdherentPoint E x0 ↔
      ∃ u : ℕ → X, (∀ n, u n ∈ E) ∧
        Filter.Tendsto u Filter.atTop (nhds x0) := by
  constructor
  · intro hAd
    have hxcl : x0 ∈ closure E :=
      (helperForProposition_1_14_isAdherentPoint_iff_mem_closure (E := E) (x0 := x0)).1 hAd
    rcases (mem_closure_iff_seq_limit).1 hxcl with ⟨u, huE, huT⟩
    exact ⟨u, huE, huT⟩
  · intro hseq
    rcases hseq with ⟨u, huE, huT⟩
    have hxcl : x0 ∈ closure E :=
      (mem_closure_iff_seq_limit).2 ⟨u, huE, huT⟩
    exact
      (helperForProposition_1_14_isAdherentPoint_iff_mem_closure (E := E) (x0 := x0)).2 hxcl

/-- Proposition 1.14: Let `(X,d)` be a metric space, `E ⊆ X`, and `x0 ∈ X`.
The following are equivalent: (a) `x0` is adherent to `E`, i.e., every `r > 0`
has `B(x0,r) ∩ E ≠ ∅`; (b) `x0` is either an interior point of `E` or a boundary
point of `E`; (c) there exists a sequence `(x_n)` in `E` with `x_n → x0`. -/
lemma proposition_1_14 {X : Type*} [MetricSpace X] (E : Set X) (x0 : X) :
    (IsAdherentPoint E x0 ↔ IsInteriorPoint E x0 ∨ IsBoundaryPoint E x0) ∧
    (IsAdherentPoint E x0 ↔
      ∃ u : ℕ → X, (∀ n, u n ∈ E) ∧
        Filter.Tendsto u Filter.atTop (nhds x0)) :=
by
  refine And.intro ?h1 ?h2
  · exact
      helperForProposition_1_14_adherent_iff_interior_or_boundary (E := E) (x0 := x0)
  · exact
      helperForProposition_1_14_adherent_iff_exists_seq_tendsto (E := E) (x0 := x0)

/-- Helper for Theorem 1.3: the closure set is the complement of the exterior set. -/
lemma helperForTheorem_1_3_closureSet_eq_compl_exteriorSet
    {X : Type*} [MetricSpace X] (E : Set X) :
    closureSet E = (exteriorSet E)ᶜ :=
by
  ext x
  constructor
  · intro hx
    change x ∉ exteriorSet E
    intro hxext
    rcases hxext with ⟨r, hrpos, hsubset⟩
    have hnon : (Metric.ball x r ∩ E).Nonempty := hx r hrpos
    rcases hnon with ⟨y, hy⟩
    have hyE : y ∈ E := hy.2
    have hycompl : y ∈ Eᶜ := hsubset hy.1
    have hycontra : y ∉ E := by
      simpa using hycompl
    exact (hycontra hyE).elim
  · intro hx
    change x ∉ exteriorSet E at hx
    intro r hrpos
    classical
    by_contra hnon
    have hsubset : Metric.ball x r ⊆ Eᶜ := by
      intro y hyBall
      change y ∉ E
      intro hyE
      apply hnon
      exact ⟨y, ⟨hyBall, hyE⟩⟩
    have hxext : x ∈ exteriorSet E := by
      exact ⟨r, hrpos, hsubset⟩
    exact (hx hxext).elim

/-- Helper for Theorem 1.3: interior union boundary equals the complement of the exterior set. -/
lemma helperForTheorem_1_3_interiorSet_union_boundarySet_eq_compl_exteriorSet
    {X : Type*} [MetricSpace X] (E : Set X) :
    interiorSet E ∪ boundarySet E = (exteriorSet E)ᶜ :=
by
  ext x
  constructor
  · intro hx
    rcases hx with hxI | hxB
    · change x ∉ exteriorSet E
      intro hxE
      have hxIntExt : x ∈ interiorSet E ∩ exteriorSet E := ⟨hxI, hxE⟩
      have hxEmpty : x ∈ (∅ : Set X) := by
        simpa [interiorSet_inter_exteriorSet_eq_empty (E := E)] using hxIntExt
      exact hxEmpty.elim
    · change x ∉ exteriorSet E
      have hxB' : ¬ IsInteriorPoint E x ∧ ¬ IsExteriorPoint E x := by
        simpa [boundarySet] using hxB
      intro hxE
      have hxE' : IsExteriorPoint E x := by
        simpa [exteriorSet] using hxE
      exact hxB'.2 hxE'
  · intro hx
    change x ∉ exteriorSet E at hx
    classical
    by_cases hI : x ∈ interiorSet E
    · exact Or.inl hI
    · right
      have hxI' : ¬ IsInteriorPoint E x := by
        simpa [interiorSet] using hI
      have hxE' : ¬ IsExteriorPoint E x := by
        intro hxE
        apply hx
        simpa [exteriorSet] using hxE
      change x ∈ boundarySet E
      exact ⟨hxI', hxE'⟩

/-- Theorem 1.3: Let `(X,d)` be a metric space and `E ⊆ X`. Define
`int(E) = {x ∈ X : ∃ r > 0, B(x,r) ⊆ E}`, `ext(E) = int(X \ E)`,
`∂E = X \ (int(E) ∪ ext(E))`, and
`\overline{E} = {x ∈ X : ∀ r > 0, B(x,r) ∩ E ≠ ∅}`.
Then `\overline{E} = int(E) ∪ ∂E = X \ ext(E)`. -/
theorem closureSet_eq_interiorSet_union_boundarySet_and_compl_exteriorSet
    {X : Type*} [MetricSpace X] (E : Set X) :
    closureSet E = interiorSet E ∪ boundarySet E ∧
    closureSet E = (exteriorSet E)ᶜ :=
by
  refine And.intro ?h1 ?h2
  · exact
      (helperForTheorem_1_3_closureSet_eq_compl_exteriorSet (E := E)).trans
        (helperForTheorem_1_3_interiorSet_union_boundarySet_eq_compl_exteriorSet (E := E)).symm
  · exact helperForTheorem_1_3_closureSet_eq_compl_exteriorSet (E := E)

/-- The closure equals the union of the interior and boundary, and equals the complement of the exterior. -/
lemma closureSet_eq_interiorSet_union_boundarySet_and_compl_exteriorSet'
    {X : Type*} [MetricSpace X] (E : Set X) :
    closureSet E = interiorSet E ∪ boundarySet E ∧
    closureSet E = (exteriorSet E)ᶜ :=
by
  exact closureSet_eq_interiorSet_union_boundarySet_and_compl_exteriorSet (E := E)

/-- Definition 1.14 (Open and closed sets): Let `(X,d)` be a metric space and `E ⊆ X`.
The set `E` is called closed if `∂E ⊆ E`. The set `E` is called open if `∂E ∩ E = ∅`. -/
def IsClosedSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  frontier E ⊆ E

/-- A set is open in the book's sense if its frontier is disjoint from it. -/
def IsOpenSet {X : Type*} [MetricSpace X] (E : Set X) : Prop :=
  frontier E ∩ E = (∅ : Set X)

/-- The book's closed-set predicate is equivalent to `IsClosed`. -/
lemma isClosedSet_iff_isClosed {X : Type*} [MetricSpace X] (E : Set X) :
    IsClosedSet E ↔ IsClosed E :=
by
  simpa [IsClosedSet] using (frontier_subset_iff_isClosed (s := E))

/-- The book's open-set predicate is equivalent to `IsOpen`. -/
lemma isOpenSet_iff_isOpen {X : Type*} [MetricSpace X] (E : Set X) :
    IsOpenSet E ↔ IsOpen E :=
by
  simpa [IsOpenSet, Set.disjoint_iff_inter_eq_empty] using
    (disjoint_frontier_iff_isOpen (s := E))

/-- Proposition 1.15: Let `(X,d)` be a metric space. Then `X` and `∅` are both open and closed
subsets of `X`. -/
lemma proposition_1_15 {X : Type*} [MetricSpace X] :
    IsOpen (Set.univ : Set X) ∧ IsClosed (Set.univ : Set X) ∧
    IsOpen (∅ : Set X) ∧ IsClosed (∅ : Set X) :=
by
  constructor
  · exact isOpen_univ
  · constructor
    · exact isClosed_univ
    · constructor
      · exact isOpen_empty
      · exact isClosed_empty

/-- In a metric space, `Set.univ` and `∅` are both open and closed. -/
lemma open_closed_univ_empty {X : Type*} [MetricSpace X] :
    IsOpen (Set.univ : Set X) ∧ IsClosed (Set.univ : Set X) ∧
    IsOpen (∅ : Set X) ∧ IsClosed (∅ : Set X) :=
by
  simpa using (proposition_1_15 (X := X))

/-- Proposition 1.16: Let `(X, d_disc)` be a set equipped with the discrete metric
`d_disc(x,y)=0` if `x=y` and `d_disc(x,y)=1` if `x≠y`. Then every subset `E ⊆ X` is
open and closed in the metric topology induced by `d_disc`. -/
lemma proposition_1_16 {X : Type*} [MetricSpace X] [DiscreteTopology X] (E : Set X) :
    IsOpen E ∧ IsClosed E :=
by
  constructor
  · simpa using (isOpen_discrete (s := E))
  · simpa using (isClosed_discrete (s := E))

/-- Helper for Proposition 1.17: the two characterizations of open sets in part (a). -/
lemma helperForProposition_1_17_part_a {X : Type*} [MetricSpace X] (E : Set X) :
    (IsOpen E ↔ E = interior E) ∧
    (IsOpen E ↔ ∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ E) :=
by
  constructor
  · simpa [eq_comm] using (interior_eq_iff_isOpen (s := E)).symm
  · simpa using (Metric.isOpen_iff (s := E))

/-- Helper for Proposition 1.17: closed sets via adherent points and sequential limits. -/
lemma helperForProposition_1_17_part_b {X : Type*} [MetricSpace X] (E : Set X) :
    (IsClosed E ↔ ∀ x, IsAdherentPoint E x → x ∈ E) ∧
    (IsClosed E ↔
      ∀ u : ℕ → X, (∀ n, u n ∈ E) →
        ∀ x, Filter.Tendsto u Filter.atTop (nhds x) → x ∈ E) :=
by
  constructor
  · constructor
    · intro hClosed x hx
      have hxcl :
          x ∈ closure E :=
        (helperForProposition_1_14_isAdherentPoint_iff_mem_closure
          (E := E) (x0 := x)).1 hx
      have hsubset : closure E ⊆ E :=
        (closure_subset_iff_isClosed (s := E)).2 hClosed
      exact hsubset hxcl
    · intro h
      have hsubset : closure E ⊆ E := by
        intro x hxcl
        have hxad :
            IsAdherentPoint E x :=
          (helperForProposition_1_14_isAdherentPoint_iff_mem_closure
            (E := E) (x0 := x)).2 hxcl
        exact h x hxad
      exact (closure_subset_iff_isClosed (s := E)).1 hsubset
  · constructor
    · intro hClosed u hu x hx
      have hEvent : ∀ᶠ n in Filter.atTop, u n ∈ E :=
        Filter.Eventually.of_forall hu
      exact IsClosed.mem_of_tendsto hClosed hx hEvent
    · intro hseq
      have hsubset : closure E ⊆ E := by
        intro x hxcl
        rcases (mem_closure_iff_seq_limit).1 hxcl with ⟨u, hu, hx⟩
        exact hseq u hu x hx
      exact (closure_subset_iff_isClosed (s := E)).1 hsubset

/-- Helper for Proposition 1.17: parts (c)-(g) on balls, complements, and unions/intersections. -/
lemma helperForProposition_1_17_parts_c_to_g {X : Type*} [MetricSpace X] :
    (∀ x0 : X, ∀ r : ℝ, 0 < r →
        IsOpen (Metric.ball x0 r) ∧ IsClosed (Metric.closedBall x0 r)) ∧
    (∀ x0 : X, IsClosed ({x0} : Set X)) ∧
    (∀ E : Set X, IsOpen E ↔ IsClosed (Eᶜ)) ∧
    (∀ n : ℕ, ∀ E : Fin n → Set X,
        (∀ i, IsOpen (E i)) → IsOpen (⋂ i, E i)) ∧
    (∀ n : ℕ, ∀ F : Fin n → Set X,
        (∀ i, IsClosed (F i)) → IsClosed (⋃ i, F i)) ∧
    (∀ {I : Type*} (E : I → Set X),
        (∀ i, IsOpen (E i)) → IsOpen (⋃ i, E i)) ∧
    (∀ {I : Type*} (F : I → Set X),
        (∀ i, IsClosed (F i)) → IsClosed (⋂ i, F i)) :=
by
  constructor
  · intro x0 r hr
    constructor
    · exact Metric.isOpen_ball
    · exact Metric.isClosed_closedBall
  · constructor
    · intro x0
      simpa using (isClosed_singleton : IsClosed ({x0} : Set X))
    · constructor
      · intro E
        simpa using (isOpen_compl_iff (s := Eᶜ))
      · constructor
        · intro n E hE
          exact isOpen_iInter_of_finite hE
        · constructor
          · intro n F hF
            exact isClosed_iUnion_of_finite hF
          · constructor
            · intro I E hE
              exact isOpen_iUnion hE
            · intro I F hF
              exact isClosed_iInter hF

/-- Helper for Proposition 1.17: interior is maximal open, closure is minimal closed. -/
lemma helperForProposition_1_17_part_h {X : Type*} [MetricSpace X] (E : Set X) :
    IsOpen (interior E) ∧
    interior E ⊆ E ∧
    (∀ V, IsOpen V → V ⊆ E → V ⊆ interior E) ∧
    IsClosed (closure E) ∧
    E ⊆ closure E ∧
    (∀ K, IsClosed K → E ⊆ K → closure E ⊆ K) :=
by
  constructor
  · exact isOpen_interior
  · constructor
    · exact interior_subset
    · constructor
      · intro V hVopen hVsub
        exact interior_maximal hVsub hVopen
      · constructor
        · exact isClosed_closure
        · constructor
          · exact subset_closure
          · intro K hK hEsub
            exact closure_minimal hEsub hK

/-- Proposition 1.17 (Basic properties of open and closed sets): Let `(X,d)` be a metric space.
(a) For `E ⊆ X`, `E` is open iff `E = int(E)`; equivalently, `E` is open iff for every `x ∈ E`
there exists `r > 0` such that `B(x,r) ⊆ E`.
(b) For `E ⊆ X`, `E` is closed iff it contains all its adherent points; equivalently, `E` is closed
iff every convergent sequence in `E` has its limit in `E`.
(c) For `x0 ∈ X` and `r > 0`, `B(x0,r)` is open and `{x ∈ X : d(x,x0) ≤ r}` is closed.
(d) For `x0 ∈ X`, the singleton `{x0}` is closed.
(e) For `E ⊆ X`, `E` is open iff `X \ E` is closed.
(f) Finite intersections of open sets are open; finite unions of closed sets are closed.
(g) Arbitrary unions of open sets are open; arbitrary intersections of closed sets are closed.
(h) For `E ⊆ X`, `int(E)` is the largest open set contained in `E`, and `\overline{E}` is the
smallest closed set containing `E`. -/
lemma proposition_1_17 {X : Type*} [MetricSpace X] :
    (∀ E : Set X,
        (IsOpen E ↔ E = interior E) ∧
        (IsOpen E ↔ ∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ E)) ∧
    (∀ E : Set X,
        (IsClosed E ↔ ∀ x, IsAdherentPoint E x → x ∈ E) ∧
        (IsClosed E ↔
          ∀ u : ℕ → X, (∀ n, u n ∈ E) →
            ∀ x, Filter.Tendsto u Filter.atTop (nhds x) → x ∈ E)) ∧
    (∀ x0 : X, ∀ r : ℝ, 0 < r →
        IsOpen (Metric.ball x0 r) ∧ IsClosed (Metric.closedBall x0 r)) ∧
    (∀ x0 : X, IsClosed ({x0} : Set X)) ∧
    (∀ E : Set X, IsOpen E ↔ IsClosed (Eᶜ)) ∧
    (∀ n : ℕ, ∀ E : Fin n → Set X,
        (∀ i, IsOpen (E i)) → IsOpen (⋂ i, E i)) ∧
    (∀ n : ℕ, ∀ F : Fin n → Set X,
        (∀ i, IsClosed (F i)) → IsClosed (⋃ i, F i)) ∧
    (∀ {I : Type*} (E : I → Set X),
        (∀ i, IsOpen (E i)) → IsOpen (⋃ i, E i)) ∧
    (∀ {I : Type*} (F : I → Set X),
        (∀ i, IsClosed (F i)) → IsClosed (⋂ i, F i)) ∧
    (∀ E : Set X,
        IsOpen (interior E) ∧
        interior E ⊆ E ∧
        (∀ V, IsOpen V → V ⊆ E → V ⊆ interior E) ∧
        IsClosed (closure E) ∧
        E ⊆ closure E ∧
        (∀ K, IsClosed K → E ⊆ K → closure E ⊆ K)) :=
by
  refine And.intro ?hA ?hrest
  · intro E
    exact helperForProposition_1_17_part_a (E := E)
  · refine And.intro ?hB ?hrest2
    · intro E
      exact helperForProposition_1_17_part_b (E := E)
    · refine And.intro ?hc ?hrest3
      · intro x0 r hr
        constructor
        · exact Metric.isOpen_ball
        · exact Metric.isClosed_closedBall
      · refine And.intro ?hd ?hrest4
        · intro x0
          simpa using (isClosed_singleton : IsClosed ({x0} : Set X))
        · refine And.intro ?he ?hrest5
          · intro E
            simpa using (isOpen_compl_iff (s := Eᶜ))
          · refine And.intro ?hf1 ?hrest6
            · intro n E hE
              exact isOpen_iInter_of_finite hE
            · refine And.intro ?hf2 ?hrest7
              · intro n F hF
                exact isClosed_iUnion_of_finite hF
              · refine And.intro ?hg1 ?hrest8
                · intro I E hE
                  exact isOpen_iUnion hE
                · refine And.intro ?hg2 ?hrest9
                  · intro I F hF
                    exact isClosed_iInter hF
                  · intro E
                    exact helperForProposition_1_17_part_h (E := E)

/-- Basic properties of open and closed sets in a metric space (Proposition 1.17). -/
lemma proposition_1_17' {X : Type*} [MetricSpace X] :
    (∀ E : Set X,
        (IsOpen E ↔ E = interior E) ∧
        (IsOpen E ↔ ∀ x ∈ E, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ E)) ∧
    (∀ E : Set X,
        (IsClosed E ↔ ∀ x, IsAdherentPoint E x → x ∈ E) ∧
        (IsClosed E ↔
          ∀ u : ℕ → X, (∀ n, u n ∈ E) →
            ∀ x, Filter.Tendsto u Filter.atTop (nhds x) → x ∈ E)) ∧
    (∀ x0 : X, ∀ r : ℝ, 0 < r →
        IsOpen (Metric.ball x0 r) ∧ IsClosed (Metric.closedBall x0 r)) ∧
    (∀ x0 : X, IsClosed ({x0} : Set X)) ∧
    (∀ E : Set X, IsOpen E ↔ IsClosed (Eᶜ)) ∧
    (∀ n : ℕ, ∀ E : Fin n → Set X,
        (∀ i, IsOpen (E i)) → IsOpen (⋂ i, E i)) ∧
    (∀ n : ℕ, ∀ F : Fin n → Set X,
        (∀ i, IsClosed (F i)) → IsClosed (⋃ i, F i)) ∧
    (∀ {I : Type*} (E : I → Set X),
        (∀ i, IsOpen (E i)) → IsOpen (⋃ i, E i)) ∧
    (∀ {I : Type*} (F : I → Set X),
        (∀ i, IsClosed (F i)) → IsClosed (⋂ i, F i)) ∧
    (∀ E : Set X,
        IsOpen (interior E) ∧
        interior E ⊆ E ∧
        (∀ V, IsOpen V → V ⊆ E → V ⊆ interior E) ∧
        IsClosed (closure E) ∧
        E ⊆ closure E ∧
        (∀ K, IsClosed K → E ⊆ K → closure E ⊆ K)) :=
by
  simpa using (proposition_1_17 (X := X))

/-- Helper for Proposition 1.35: `Ico (1,2)` is not open in `ℝ`. -/
lemma real_Ico_one_two_not_isOpen : ¬ IsOpen (Set.Ico (1 : ℝ) 2) :=
by
  intro hopen
  have hInterior : interior (Set.Ico (1 : ℝ) 2) = Set.Ico (1 : ℝ) 2 :=
    IsOpen.interior_eq hopen
  have hEq : Set.Ico (1 : ℝ) 2 = Set.Ioo (1 : ℝ) 2 := by
    calc
      Set.Ico (1 : ℝ) 2 = interior (Set.Ico (1 : ℝ) 2) := by
        symm
        exact hInterior
      _ = Set.Ioo (1 : ℝ) 2 := helperForProposition_1_12_interior_Ico
  have hmem : (1 : ℝ) ∈ Set.Ico (1 : ℝ) 2 := by
    simp [Set.mem_Ico]
  have hmem' : (1 : ℝ) ∈ Set.Ioo (1 : ℝ) 2 := by
    simpa [hEq] using hmem
  have hnot : (1 : ℝ) ∉ Set.Ioo (1 : ℝ) 2 := by
    simp [Set.mem_Ioo]
  exact (hnot hmem').elim

/-- Helper for Proposition 1.35: `Ico (1,2)` is not closed in `ℝ`. -/
lemma real_Ico_one_two_not_isClosed : ¬ IsClosed (Set.Ico (1 : ℝ) 2) :=
by
  intro hclosed
  have hclosure : closure (Set.Ico (1 : ℝ) 2) = Set.Ico (1 : ℝ) 2 :=
    IsClosed.closure_eq hclosed
  have hne : (1 : ℝ) ≠ 2 := ne_of_lt helperForProposition_1_12_one_lt_two
  have hclosureIcc : closure (Set.Ico (1 : ℝ) 2) = Set.Icc (1 : ℝ) 2 := by
    simpa using (closure_Ico (a := (1 : ℝ)) (b := 2) hne)
  have hmemIcc : (2 : ℝ) ∈ Set.Icc (1 : ℝ) 2 := by
    exact ⟨le_of_lt helperForProposition_1_12_one_lt_two, le_rfl⟩
  have hmemClosure : (2 : ℝ) ∈ closure (Set.Ico (1 : ℝ) 2) := by
    rw [hclosureIcc]
    exact hmemIcc
  have hmemIco : (2 : ℝ) ∈ Set.Ico (1 : ℝ) 2 := by
    rw [← hclosure]
    exact hmemClosure
  have hnot : (2 : ℝ) ∉ Set.Ico (1 : ℝ) 2 := by
    simp [Set.mem_Ico]
  exact (hnot hmemIco).elim

/-- Helper for Proposition 1.35: the lifted `Ico (1,2)` is not open. -/
lemma ulift_Ico_one_two_not_isOpen :
    ¬ IsOpen ((ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2) :=
by
  intro hopen
  have hpre :
      IsOpen (ULift.up ⁻¹' ((ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2)) :=
    (ULift.isOpen_iff (s := (ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2)).1 hopen
  have hopen' : IsOpen (Set.Ico (1 : ℝ) 2) := by
    simpa using hpre
  exact real_Ico_one_two_not_isOpen hopen'

/-- Helper for Proposition 1.35: the lifted `Ico (1,2)` is not closed. -/
lemma ulift_Ico_one_two_not_isClosed :
    ¬ IsClosed ((ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2) :=
by
  intro hclosed
  have hpre :
      IsClosed (ULift.up ⁻¹' ((ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2)) :=
    (ULift.isClosed_iff (s := (ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2)).1 hclosed
  have hpre_eq :
      (ULift.up ⁻¹' ((ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2)) =
        Set.Ico (1 : ℝ) 2 := by
    ext x
    rfl
  have hclosed' : IsClosed (Set.Ico (1 : ℝ) 2) := by
    rw [← hpre_eq]
    exact hpre
  exact real_Ico_one_two_not_isClosed hclosed'

/-- Proposition 1.35 (Open and closed are not complementary notions): Let `(X,d)` be a metric space.
(1) There exist subsets of `X` that are both open and closed (e.g., `X` itself and `∅`).
(2) There may exist subsets of `X` that are neither open nor closed.
(3) A subset `E ⊆ X` is open iff its complement `X \ E` is closed.
In particular, knowing that a set is not open does not imply that it is closed, and vice versa. -/
lemma proposition_1_35 :
    (∀ {X : Type*} [MetricSpace X], IsOpen (Set.univ : Set X) ∧ IsClosed (Set.univ : Set X) ∧
      IsOpen (∅ : Set X) ∧ IsClosed (∅ : Set X)) ∧
    (∃ (X : Type*), ∃ h : MetricSpace X, ∃ E : Set X, ¬ IsOpen E ∧ ¬ IsClosed E) ∧
    (∀ {X : Type*} [MetricSpace X], ∀ E : Set X, IsOpen E ↔ IsClosed (Eᶜ)) :=
by
  constructor
  · intro X
    intro inst
    constructor
    · exact isOpen_univ
    · constructor
      · exact isClosed_univ
      · constructor
        · exact isOpen_empty
        · exact isClosed_empty
  · constructor
    · refine ⟨ULift ℝ, inferInstance,
        (ULift.down : ULift ℝ → ℝ) ⁻¹' Set.Ico (1 : ℝ) 2, ?_, ?_⟩
      · exact ulift_Ico_one_two_not_isOpen
      · exact ulift_Ico_one_two_not_isClosed
    · intro X
      intro inst
      intro E
      simpa using (isClosed_compl_iff (s := E)).symm

end Section02
end Chap01

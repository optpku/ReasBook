/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

/-- Definition 39.0.1: A convex process from `ℝ^m` to `ℝ^n` is a set-valued mapping `A : u ↦ A u`
satisfying:

(a) `A (u₁ + u₂) ⊇ A u₁ + A u₂` for all `u₁, u₂`,

(b) `A (λ • u) = λ • A u` for all `u` and all `λ > 0`,

(c) `0 ∈ A 0`. -/
structure ConvexProcess (m n : ℕ) where
  /-- The underlying set-valued mapping `u ↦ A u`. -/
  toSetValued : (Fin m → ℝ) → Set (Fin n → ℝ)
  /-- (a) Superadditivity with respect to pointwise (Minkowski) addition of sets. -/
  map_add_superset :
    ∀ u₁ u₂, toSetValued u₁ + toSetValued u₂ ⊆ toSetValued (u₁ + u₂)
  /-- (b) Positive homogeneity with respect to pointwise scalar multiplication of sets. -/
  map_smul_pos :
    ∀ u (r : ℝ), 0 < r → toSetValued (r • u) = r • toSetValued u
  /-- (c) The origin is in the image of the origin. -/
  zero_mem : (0 : (Fin n → ℝ)) ∈ toSetValued (0 : (Fin m → ℝ))

/-- The graph of a set-valued mapping `A : (Fin m → ℝ) → Set (Fin n → ℝ)`, as a subset of
`(Fin m → ℝ) × (Fin n → ℝ)` (identified with `ℝ^(m+n)`). -/
def setValuedGraph {m n : ℕ} (A : (Fin m → ℝ) → Set (Fin n → ℝ)) :
    Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  { p | p.2 ∈ A p.1 }

/-- Helper for Proposition 39.0.1: graph add closure follows from convex-process superadditivity. -/
lemma helperForProposition_39_0_1_graph_add_closed_ofConvexProcess {m n : ℕ}
    (cp : ConvexProcess m n) {p q : (Fin m → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ setValuedGraph cp.toSetValued) (hq : q ∈ setValuedGraph cp.toSetValued) :
    p + q ∈ setValuedGraph cp.toSetValued := by
  -- Convert graph membership into fiber membership and invoke the process superadditivity axiom.
  rcases p with ⟨u₁, x₁⟩
  rcases q with ⟨u₂, x₂⟩
  simp only [setValuedGraph] at hp hq ⊢
  have hsum : x₁ + x₂ ∈ cp.toSetValued u₁ + cp.toSetValued u₂ :=
    Set.mem_add.2 ⟨x₁, hp, x₂, hq, rfl⟩
  exact cp.map_add_superset u₁ u₂ hsum

/-- Helper for Proposition 39.0.1: this packages graph add closure in the field order of
`ConvexCone`. -/
lemma helperForProposition_39_0_1_graph_add_mem_ofConvexProcess {m n : ℕ}
    (cp : ConvexProcess m n) :
    ∀ ⦃p : (Fin m → ℝ) × (Fin n → ℝ)⦄, p ∈ setValuedGraph cp.toSetValued →
      ∀ ⦃q : (Fin m → ℝ) × (Fin n → ℝ)⦄, q ∈ setValuedGraph cp.toSetValued →
        p + q ∈ setValuedGraph cp.toSetValued := by
  -- Reorder the arguments so the lemma can be used directly as a `ConvexCone` field.
  intro p hp q hq
  exact helperForProposition_39_0_1_graph_add_closed_ofConvexProcess cp hp hq

/-- Helper for Proposition 39.0.1: graph positive-scale closure follows from convex-process
positive homogeneity. -/
lemma helperForProposition_39_0_1_graph_smul_pos_closed_ofConvexProcess {m n : ℕ}
    (cp : ConvexProcess m n) {r : ℝ} (hr : 0 < r)
    {p : (Fin m → ℝ) × (Fin n → ℝ)}
    (hp : p ∈ setValuedGraph cp.toSetValued) :
    r • p ∈ setValuedGraph cp.toSetValued := by
  -- Rewrite the scaled graph point componentwise and use positive homogeneity of the process.
  rcases p with ⟨u, x⟩
  simp only [setValuedGraph, Prod.smul_mk] at hp ⊢
  have hx : r • x ∈ r • cp.toSetValued u :=
    Set.mem_smul_set.2 ⟨x, hp, rfl⟩
  simpa [cp.map_smul_pos u r hr] using hx

/-- Helper for Proposition 39.0.1: this packages graph positive-scale closure in the field order of
`ConvexCone`. -/
lemma helperForProposition_39_0_1_graph_smul_mem_ofConvexProcess {m n : ℕ}
    (cp : ConvexProcess m n) :
    ∀ ⦃r : ℝ⦄, 0 < r → ∀ ⦃p : (Fin m → ℝ) × (Fin n → ℝ)⦄,
      p ∈ setValuedGraph cp.toSetValued → r • p ∈ setValuedGraph cp.toSetValued := by
  -- Reorder the arguments so the lemma can be used directly as a `ConvexCone` field.
  intro r hr p hp
  exact helperForProposition_39_0_1_graph_smul_pos_closed_ofConvexProcess cp hr hp

/-- Helper for Proposition 39.0.1: a graph cone yields the convex-process superadditivity axiom. -/
lemma helperForProposition_39_0_1_map_add_superset_ofGraphCone {m n : ℕ}
    (A : (Fin m → ℝ) → Set (Fin n → ℝ))
    (C : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)))
    (hgraph : (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) = setValuedGraph A) :
    ∀ u₁ u₂, A u₁ + A u₂ ⊆ A (u₁ + u₂) := by
  intro u₁ u₂ x hx
  -- Lift both fiber witnesses to graph points and add them inside the cone.
  rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  have hx₁C : (u₁, x₁) ∈ C := by
    change (u₁, x₁) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ)))
    rw [hgraph]
    simpa [setValuedGraph] using hx₁
  have hx₂C : (u₂, x₂) ∈ C := by
    change (u₂, x₂) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ)))
    rw [hgraph]
    simpa [setValuedGraph] using hx₂
  have hsumC : (u₁, x₁) + (u₂, x₂) ∈ C := C.add_mem hx₁C hx₂C
  change ((u₁, x₁) + (u₂, x₂)) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) at hsumC
  rw [hgraph] at hsumC
  simpa [setValuedGraph] using hsumC

/-- Helper for Proposition 39.0.1: a graph cone yields the convex-process positive-homogeneity
axiom. -/
lemma helperForProposition_39_0_1_map_smul_pos_ofGraphCone {m n : ℕ}
    (A : (Fin m → ℝ) → Set (Fin n → ℝ))
    (C : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)))
    (hgraph : (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) = setValuedGraph A) :
    ∀ u (r : ℝ), 0 < r → A (r • u) = r • A u := by
  intro u r hr
  ext x
  constructor
  · intro hx
    -- Descend along the cone by `r⁻¹` to recover a graph point over `u`.
    have hxC : (r • u, x) ∈ C := by
      change (r • u, x) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ)))
      rw [hgraph]
      simpa [setValuedGraph] using hx
    have hdescaled : (r⁻¹ : ℝ) • (r • u, x) ∈ C :=
      C.smul_mem (inv_pos.2 hr) hxC
    have hy : (r⁻¹ : ℝ) • x ∈ A u := by
      change (r⁻¹ : ℝ) • (r • u, x) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) at hdescaled
      rw [hgraph] at hdescaled
      simpa [setValuedGraph, Prod.smul_mk, smul_smul, hr.ne'] using hdescaled
    refine Set.mem_smul_set.2 ?_
    refine ⟨(r⁻¹ : ℝ) • x, hy, ?_⟩
    simp [smul_smul, hr.ne']
  · intro hx
    -- Scale the graph point `(u,y)` directly inside the cone for the reverse inclusion.
    rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
    have hyC : (u, y) ∈ C := by
      change (u, y) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ)))
      rw [hgraph]
      simpa [setValuedGraph] using hy
    have hscaled : r • (u, y) ∈ C := C.smul_mem hr hyC
    change r • (u, y) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) at hscaled
    rw [hgraph] at hscaled
    simpa [setValuedGraph, Prod.smul_mk] using hscaled

/-- Helper for Proposition 39.0.1: origin membership in the graph is exactly `0 ∈ A 0`. -/
lemma helperForProposition_39_0_1_zero_mem_ofGraphZero {m n : ℕ}
    (A : (Fin m → ℝ) → Set (Fin n → ℝ))
    (hzero : (0 : ((Fin m → ℝ) × (Fin n → ℝ))) ∈ setValuedGraph A) :
    (0 : Fin n → ℝ) ∈ A 0 := by
  -- Unpack graph membership at the origin.
  simpa [setValuedGraph] using hzero

/-- Helper for Proposition 39.0.1: package the graph of a convex process as a convex cone. -/
def helperForProposition_39_0_1_graphConvexCone_ofConvexProcess {m n : ℕ}
    (cp : ConvexProcess m n) :
    ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)) :=
  { carrier := setValuedGraph cp.toSetValued
    smul_mem' := helperForProposition_39_0_1_graph_smul_mem_ofConvexProcess cp
    add_mem' := helperForProposition_39_0_1_graph_add_mem_ofConvexProcess cp }

/-- Helper for Proposition 39.0.1: a graph cone together with origin membership reconstructs the
corresponding convex process. -/
lemma helperForProposition_39_0_1_exists_convexProcess_ofGraphCone {m n : ℕ}
    (A : (Fin m → ℝ) → Set (Fin n → ℝ))
    (C : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)))
    (hgraph : (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) = setValuedGraph A)
    (hzero : (0 : ((Fin m → ℝ) × (Fin n → ℝ))) ∈ setValuedGraph A) :
    ∃ cp : ConvexProcess m n, cp.toSetValued = A := by
  -- Assemble the three recovered graph-closure facts into the structure fields of `ConvexProcess`.
  refine ⟨{
    toSetValued := A
    map_add_superset := helperForProposition_39_0_1_map_add_superset_ofGraphCone A C hgraph
    map_smul_pos := helperForProposition_39_0_1_map_smul_pos_ofGraphCone A C hgraph
    zero_mem := helperForProposition_39_0_1_zero_mem_ofGraphZero A hzero
  }, rfl⟩

-- Proof sketch: Expand both definitions. `ConvexProcess` axioms translate to closure of the graph
-- under addition and under scaling by `r > 0`, and the `zero_mem` axiom gives `(0,0)` in the graph;
-- conversely, use these closure properties of the graph to recover (a), (b), (c) for `A`.
/-- Proposition 39.0.1: A set-valued mapping `A : ℝ^m ⇉ ℝ^n` is a convex process if and only if its
graph is a convex cone in `ℝ^(m+n)` containing the origin. -/
theorem convexProcess_iff_graph_isConvexCone {m n : ℕ}
    (A : (Fin m → ℝ) → Set (Fin n → ℝ)) :
    (∃ cp : ConvexProcess m n, cp.toSetValued = A) ↔
      ((∃ C : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)), (C : Set _) = setValuedGraph A) ∧
        (0 : ((Fin m → ℝ) × (Fin n → ℝ))) ∈ setValuedGraph A) :=
  by
  constructor
  · rintro ⟨cp, rfl⟩
    -- Package the graph of a convex process as a convex cone using the dedicated helper object.
    let C := helperForProposition_39_0_1_graphConvexCone_ofConvexProcess cp
    refine ⟨?_, ?_⟩
    · exact ⟨C, rfl⟩
    · -- The process axiom `0 ∈ A 0` is exactly origin membership in the graph.
      simpa [setValuedGraph] using cp.zero_mem
  · rintro ⟨⟨C, hgraph⟩, hzero⟩
    -- Recover the convex-process axioms from cone closure via the converse helper.
    exact helperForProposition_39_0_1_exists_convexProcess_ofGraphCone A C hgraph hzero

/-- The domain of a set-valued mapping `A : X → Set Y`, defined as `{x | A x ≠ ∅}`. -/
def setValuedDom {X Y : Type*} (A : X → Set Y) : Set X :=
  { x | (A x).Nonempty }

/-- The range of a set-valued mapping `A : X → Set Y`, defined as `⋃ x, A x`. -/
def setValuedRange {X Y : Type*} (A : X → Set Y) : Set Y :=
  { y | ∃ x, y ∈ A x }

/-- The inverse of a set-valued mapping `A : X → Set Y`, defined by `A⁻¹ y = {x | y ∈ A x}`. -/
def setValuedInverse {X Y : Type*} (A : X → Set Y) : Y → Set X :=
  fun y => { x | y ∈ A x }

/-- The generic set-valued identity `dom (A⁻¹) = range A`. -/
lemma setValuedDom_setValuedInverse_eq_setValuedRange {X Y : Type*} (A : X → Set Y) :
    setValuedDom (setValuedInverse A) = setValuedRange A := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩

namespace ConvexProcess

/-- The domain of a convex process `A`, defined as `{u | A u ≠ ∅}`. -/
def dom {m n : ℕ} (A : ConvexProcess m n) : Set (Fin m → ℝ) :=
  setValuedDom A.toSetValued

/-- The range of a convex process `A`, defined as `⋃ u, A u`. -/
def range {m n : ℕ} (A : ConvexProcess m n) : Set (Fin n → ℝ) :=
  setValuedRange A.toSetValued

/-- The inverse set-valued mapping `A⁻¹` associated to a convex process `A`. -/
def inverseMap {m n : ℕ} (A : ConvexProcess m n) : (Fin n → ℝ) → Set (Fin m → ℝ) :=
  setValuedInverse A.toSetValued

end ConvexProcess

-- Proof sketch: Use Proposition 39.0.1 to pass to the graph, which is a convex cone in `ℝ^(m+n)`
-- containing `(0,0)`. Projections and fibers of a convex cone are convex, the origin fiber is a cone,
-- and the set-inclusion characterizations (ii) and (v) follow by unpacking definitions of pointwise
-- (Minkowski) addition, domain/range as (non)emptiness and union, and inverse image `A⁻¹`.
/-- Helper for Proposition 39.0.2: a fiber of a convex process is closed under convex
combinations. -/
lemma helperForProposition_39_0_2_fiber_combo_mem {m n : ℕ} (A : ConvexProcess m n)
    {u : Fin m → ℝ} {x₁ x₂ : Fin n → ℝ} {t : ℝ}
    (hx₁ : x₁ ∈ A.toSetValued u) (hx₂ : x₂ ∈ A.toSetValued u)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    t • x₁ + (1 - t) • x₂ ∈ A.toSetValued u := by
  rcases ht with ⟨ht0, ht1⟩
  by_cases ht_zero : t = 0
  · -- At the left endpoint, the convex combination collapses to `x₂`.
    subst ht_zero
    simpa using hx₂
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (by simpa [eq_comm] using ht_zero)
    by_cases ht_one : t = 1
    · -- At the right endpoint, the convex combination collapses to `x₁`.
      subst ht_one
      simpa using hx₁
    · have h_one_sub_pos : 0 < 1 - t := sub_pos.mpr (lt_of_le_of_ne ht1 ht_one)
      -- Positive homogeneity moves each point into the correspondingly scaled fiber.
      have hx₁_scaled : t • x₁ ∈ A.toSetValued (t • u) := by
        have hx₁_mem : t • x₁ ∈ t • A.toSetValued u :=
          Set.mem_smul_set.2 ⟨x₁, hx₁, rfl⟩
        simpa [A.map_smul_pos u t ht_pos] using hx₁_mem
      have hx₂_scaled : (1 - t) • x₂ ∈ A.toSetValued ((1 - t) • u) := by
        have hx₂_mem : (1 - t) • x₂ ∈ (1 - t) • A.toSetValued u :=
          Set.mem_smul_set.2 ⟨x₂, hx₂, rfl⟩
        simpa [A.map_smul_pos u (1 - t) h_one_sub_pos] using hx₂_mem
      -- Superadditivity combines the two scaled fibers back into the original fiber.
      have hsum :
          t • x₁ + (1 - t) • x₂ ∈
            A.toSetValued (t • u) + A.toSetValued ((1 - t) • u) :=
        Set.mem_add.2 ⟨t • x₁, hx₁_scaled, (1 - t) • x₂, hx₂_scaled, rfl⟩
      have hmem :
          t • x₁ + (1 - t) • x₂ ∈
            A.toSetValued (t • u + (1 - t) • u) :=
        A.map_add_superset (t • u) ((1 - t) • u) hsum
      have hu : t • u + (1 - t) • u = u := by
        ext i
        change t * u i + (1 - t) * u i = u i
        ring
      simpa [hu] using hmem

/-- Helper for Proposition 39.0.2: the zero fiber is closed under positive scaling. -/
lemma helperForProposition_39_0_2_zeroFiber_smul_mem {m n : ℕ} (A : ConvexProcess m n)
    :
    ∀ ⦃r : ℝ⦄, 0 < r → ∀ ⦃y : Fin n → ℝ⦄, y ∈ A.toSetValued 0 →
      r • y ∈ A.toSetValued 0 := by
  intro r hr y hy
  -- Positive homogeneity at the origin identifies the zero fiber with its positive dilates.
  have hy_scaled : r • y ∈ r • A.toSetValued (0 : Fin m → ℝ) :=
    Set.mem_smul_set.2 ⟨y, hy, rfl⟩
  have hzero :
      A.toSetValued (0 : Fin m → ℝ) = r • A.toSetValued (0 : Fin m → ℝ) := by
    simpa [smul_zero] using A.map_smul_pos (0 : Fin m → ℝ) r hr
  rw [hzero]
  exact hy_scaled

/-- Helper for Proposition 39.0.2: the zero fiber is closed under addition. -/
lemma helperForProposition_39_0_2_zeroFiber_add_mem {m n : ℕ} (A : ConvexProcess m n)
    :
    ∀ ⦃y₁ : Fin n → ℝ⦄, y₁ ∈ A.toSetValued 0 → ∀ ⦃y₂ : Fin n → ℝ⦄, y₂ ∈ A.toSetValued 0 →
      y₁ + y₂ ∈ A.toSetValued 0 := by
  intro y₁ hy₁ y₂ hy₂
  -- Superadditivity at `u₁ = u₂ = 0` keeps sums inside the zero fiber.
  have hsum : y₁ + y₂ ∈ A.toSetValued (0 : Fin m → ℝ) + A.toSetValued 0 :=
    Set.mem_add.2 ⟨y₁, hy₁, y₂, hy₂, rfl⟩
  simpa using A.map_add_superset (0 : Fin m → ℝ) 0 hsum

/-- Helper for Proposition 39.0.2: the zero fiber is a convex cone and exactly the translation
invariant directions of the process. -/
lemma helperForProposition_39_0_2_zeroFiber_cone_and_stability {m n : ℕ} (A : ConvexProcess m n) :
    ((∃ C : ConvexCone ℝ (Fin n → ℝ), (C : Set _) = A.toSetValued 0) ∧
      (0 : Fin n → ℝ) ∈ A.toSetValued 0) ∧
      A.toSetValued 0 =
        { y | ∀ u, A.toSetValued u + ({y} : Set (Fin n → ℝ)) ⊆ A.toSetValued u } := by
  let C : ConvexCone ℝ (Fin n → ℝ) :=
    { carrier := A.toSetValued 0
      smul_mem' := helperForProposition_39_0_2_zeroFiber_smul_mem A
      add_mem' := helperForProposition_39_0_2_zeroFiber_add_mem A }
  constructor
  · -- Package the cone witness together with the existing origin point.
    exact ⟨⟨C, rfl⟩, A.zero_mem⟩
  · -- The zero fiber is exactly the set of directions that preserve every fiber under translation.
    ext v
    constructor
    · intro hy
      change ∀ u, A.toSetValued u + ({v} : Set (Fin n → ℝ)) ⊆ A.toSetValued u
      intro u z hz
      rcases Set.mem_add.1 hz with ⟨x, hx, y', hy', rfl⟩
      have hy'_eq : y' = v := by simpa using hy'
      subst y'
      have hsum : x + v ∈ A.toSetValued u + A.toSetValued 0 :=
        Set.mem_add.2 ⟨x, hx, v, hy, rfl⟩
      have hmem : x + v ∈ A.toSetValued (u + 0) := A.map_add_superset u 0 hsum
      simpa using hmem
    · intro hy
      have hy_stable : ∀ u, A.toSetValued u + ({v} : Set (Fin n → ℝ)) ⊆ A.toSetValued u := by
        simpa using hy
      -- Apply the translation invariance at `u = 0` to the point `0 + v`.
      have hsum : (0 : Fin n → ℝ) + v ∈
          A.toSetValued (0 : Fin m → ℝ) + ({v} : Set (Fin n → ℝ)) :=
        Set.mem_add.2 ⟨0, A.zero_mem, v, by simp, by simp⟩
      have hmem : (0 : Fin n → ℝ) + v ∈ A.toSetValued (0 : Fin m → ℝ) := hy_stable 0 hsum
      simpa using hmem

/-- Helper for Proposition 39.0.2: the domain is closed under positive scaling. -/
lemma helperForProposition_39_0_2_dom_smul_mem {m n : ℕ} (A : ConvexProcess m n)
    :
    ∀ ⦃r : ℝ⦄, 0 < r → ∀ ⦃u : Fin m → ℝ⦄, u ∈ A.dom → r • u ∈ A.dom := by
  intro r hr u hu
  change (A.toSetValued (r • u)).Nonempty
  change (A.toSetValued u).Nonempty at hu
  rcases hu with ⟨x, hx⟩
  -- Scale a witness from `A u` into a witness for `A (r • u)`.
  have hx_scaled : r • x ∈ A.toSetValued (r • u) := by
    have hx_mem : r • x ∈ r • A.toSetValued u := Set.mem_smul_set.2 ⟨x, hx, rfl⟩
    simpa [A.map_smul_pos u r hr] using hx_mem
  exact ⟨r • x, hx_scaled⟩

/-- Helper for Proposition 39.0.2: the domain is closed under addition. -/
lemma helperForProposition_39_0_2_dom_add_mem {m n : ℕ} (A : ConvexProcess m n)
    :
    ∀ ⦃u₁ : Fin m → ℝ⦄, u₁ ∈ A.dom → ∀ ⦃u₂ : Fin m → ℝ⦄, u₂ ∈ A.dom →
      u₁ + u₂ ∈ A.dom := by
  intro u₁ hu₁ u₂ hu₂
  change (A.toSetValued (u₁ + u₂)).Nonempty
  change (A.toSetValued u₁).Nonempty at hu₁
  change (A.toSetValued u₂).Nonempty at hu₂
  rcases hu₁ with ⟨x₁, hx₁⟩
  rcases hu₂ with ⟨x₂, hx₂⟩
  -- Add witnesses from the two fibers and transport them along superadditivity.
  have hsum : x₁ + x₂ ∈ A.toSetValued u₁ + A.toSetValued u₂ :=
    Set.mem_add.2 ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  exact ⟨x₁ + x₂, A.map_add_superset u₁ u₂ hsum⟩

/-- Helper for Proposition 39.0.2: the range is closed under positive scaling. -/
lemma helperForProposition_39_0_2_range_smul_mem {m n : ℕ} (A : ConvexProcess m n)
    :
    ∀ ⦃r : ℝ⦄, 0 < r → ∀ ⦃y : Fin n → ℝ⦄, y ∈ A.range → r • y ∈ A.range := by
  intro r hr y hy
  rcases hy with ⟨u, hu⟩
  -- Scale both the domain witness and the range point simultaneously.
  refine ⟨r • u, ?_⟩
  have hy_scaled : r • y ∈ r • A.toSetValued u := Set.mem_smul_set.2 ⟨y, hu, rfl⟩
  simpa [A.map_smul_pos u r hr] using hy_scaled

/-- Helper for Proposition 39.0.2: the range is closed under addition. -/
lemma helperForProposition_39_0_2_range_add_mem {m n : ℕ} (A : ConvexProcess m n)
    :
    ∀ ⦃y₁ : Fin n → ℝ⦄, y₁ ∈ A.range → ∀ ⦃y₂ : Fin n → ℝ⦄, y₂ ∈ A.range →
      y₁ + y₂ ∈ A.range := by
  intro y₁ hy₁ y₂ hy₂
  rcases hy₁ with ⟨u₁, hu₁⟩
  rcases hy₂ with ⟨u₂, hu₂⟩
  -- Superadditivity combines range witnesses from two fibers into one witness over `u₁ + u₂`.
  refine ⟨u₁ + u₂, ?_⟩
  have hsum : y₁ + y₂ ∈ A.toSetValued u₁ + A.toSetValued u₂ :=
    Set.mem_add.2 ⟨y₁, hu₁, y₂, hu₂, rfl⟩
  exact A.map_add_superset u₁ u₂ hsum

/-- Helper for Proposition 39.0.2: the domain and range are convex cones containing the origin. -/
lemma helperForProposition_39_0_2_dom_range_cones {m n : ℕ} (A : ConvexProcess m n) :
    ((∃ C : ConvexCone ℝ (Fin m → ℝ), (C : Set _) = A.dom) ∧
      (0 : Fin m → ℝ) ∈ A.dom) ∧
      ((∃ C : ConvexCone ℝ (Fin n → ℝ), (C : Set _) = A.range) ∧
        (0 : Fin n → ℝ) ∈ A.range) := by
  let Cdom : ConvexCone ℝ (Fin m → ℝ) :=
    { carrier := A.dom
      smul_mem' := helperForProposition_39_0_2_dom_smul_mem A
      add_mem' := helperForProposition_39_0_2_dom_add_mem A }
  let Crange : ConvexCone ℝ (Fin n → ℝ) :=
    { carrier := A.range
      smul_mem' := helperForProposition_39_0_2_range_smul_mem A
      add_mem' := helperForProposition_39_0_2_range_add_mem A }
  constructor
  · -- The zero fiber already supplies a witness showing `0 ∈ dom A`.
    exact ⟨⟨Cdom, rfl⟩, ⟨0, A.zero_mem⟩⟩
  · -- The same origin point lies in the range with witness `u = 0`.
    exact ⟨⟨Crange, rfl⟩, ⟨0, A.zero_mem⟩⟩

/-- Helper for Proposition 39.0.2: the origin belongs to the inverse process at the origin. -/
lemma helperForProposition_39_0_2_inverseMap_zero_mem {m n : ℕ} (A : ConvexProcess m n) :
    (0 : Fin m → ℝ) ∈ A.inverseMap (0 : Fin n → ℝ) := by
  -- This is just the original process axiom `0 ∈ A 0`.
  change (0 : Fin n → ℝ) ∈ A.toSetValued (0 : Fin m → ℝ)
  exact A.zero_mem

/-- Helper for Proposition 39.0.2: the inverse set-valued map is superadditive. -/
lemma helperForProposition_39_0_2_inverseMap_add_superset {m n : ℕ} (A : ConvexProcess m n) :
    ∀ u₁ u₂, A.inverseMap u₁ + A.inverseMap u₂ ⊆ A.inverseMap (u₁ + u₂) := by
  intro u₁ u₂ v hv
  rcases Set.mem_add.1 hv with ⟨v₁, hv₁, v₂, hv₂, rfl⟩
  -- Unfold inverse membership and push the range witnesses through superadditivity.
  change u₁ + u₂ ∈ A.toSetValued (v₁ + v₂)
  change u₁ ∈ A.toSetValued v₁ at hv₁
  change u₂ ∈ A.toSetValued v₂ at hv₂
  have hsum : u₁ + u₂ ∈ A.toSetValued v₁ + A.toSetValued v₂ :=
    Set.mem_add.2 ⟨u₁, hv₁, u₂, hv₂, rfl⟩
  exact A.map_add_superset v₁ v₂ hsum

/-- Helper for Proposition 39.0.2: the inverse set-valued map is positively homogeneous. -/
lemma helperForProposition_39_0_2_inverseMap_smul_pos {m n : ℕ} (A : ConvexProcess m n) :
    ∀ u (r : ℝ), 0 < r → A.inverseMap (r • u) = r • A.inverseMap u := by
  intro u r hr
  ext v
  constructor
  · intro hv
    -- Descale the domain witness using positive homogeneity of the original process.
    change r • u ∈ A.toSetValued v at hv
    have hu_mem : u ∈ A.toSetValued (r⁻¹ • v) := by
      have hu_scaled : u ∈ r⁻¹ • A.toSetValued v := by
        refine Set.mem_smul_set.2 ?_
        exact ⟨r • u, hv, by simp [smul_smul, hr.ne']⟩
      simpa [ConvexProcess.inverseMap, ConvexProcess.dom, setValuedInverse, A.map_smul_pos v r⁻¹ (inv_pos.2 hr)] using hu_scaled
    change v ∈ r • A.inverseMap u
    refine Set.mem_smul_set.2 ?_
    exact ⟨r⁻¹ • v, hu_mem, by simp [smul_smul, hr.ne']⟩
  · intro hv
    change v ∈ r • A.inverseMap u at hv
    rcases Set.mem_smul_set.1 hv with ⟨v', hv', rfl⟩
    change u ∈ A.toSetValued v' at hv'
    change r • u ∈ A.toSetValued (r • v')
    -- Scale the inverse witness back up inside the original process.
    have hu_scaled : r • u ∈ r • A.toSetValued v' := Set.mem_smul_set.2 ⟨u, hv', rfl⟩
    simpa [ConvexProcess.inverseMap, setValuedInverse, A.map_smul_pos v' r hr] using hu_scaled

/-- Helper for Proposition 39.0.2: the inverse mapping is a convex process and it swaps domain and
range. -/
lemma helperForProposition_39_0_2_inverseProcess_and_dom_range {m n : ℕ} (A : ConvexProcess m n) :
    (∃ Ainv : ConvexProcess n m, Ainv.toSetValued = A.inverseMap) ∧
      setValuedDom A.inverseMap = A.range ∧
      setValuedRange A.inverseMap = A.dom := by
  let Ainv : ConvexProcess n m :=
    { toSetValued := A.inverseMap
      map_add_superset := helperForProposition_39_0_2_inverseMap_add_superset A
      map_smul_pos := helperForProposition_39_0_2_inverseMap_smul_pos A
      zero_mem := helperForProposition_39_0_2_inverseMap_zero_mem A }
  refine ⟨⟨Ainv, rfl⟩, ?_, ?_⟩
  · -- Domain of the inverse is exactly the range of the original process.
    ext y
    constructor
    · intro hy
      change (A.inverseMap y).Nonempty at hy
      rcases hy with ⟨u, hu⟩
      exact ⟨u, hu⟩
    · intro hy
      rcases hy with ⟨u, hu⟩
      change (A.inverseMap y).Nonempty
      exact ⟨u, hu⟩
  · -- Range of the inverse is exactly the domain of the original process.
    ext u
    constructor
    · intro hu
      rcases hu with ⟨y, hy⟩
      exact ⟨y, hy⟩
    · intro hu
      change (A.toSetValued u).Nonempty at hu
      rcases hu with ⟨y, hy⟩
      exact ⟨y, hy⟩

/-- Helper for Proposition 39.0.2: the inverse fiber at the origin is the shift-invariant set of
directions. -/
lemma helperForProposition_39_0_2_inverse_zero_eq_shiftInvariant {m n : ℕ} (A : ConvexProcess m n) :
    A.inverseMap (0 : Fin n → ℝ) =
      { v | ∀ u, A.toSetValued u ⊆ A.toSetValued (u + v) } := by
  ext v
  constructor
  · intro hv
    change (0 : Fin n → ℝ) ∈ A.toSetValued v at hv
    change ∀ u, A.toSetValued u ⊆ A.toSetValued (u + v)
    intro u x hx
    -- Add the zero-fiber witness `0 ∈ A v` to an arbitrary point of `A u`.
    have hsum : x + 0 ∈ A.toSetValued u + A.toSetValued v :=
      Set.mem_add.2 ⟨x, hx, 0, hv, by simp⟩
    have hmem : x + 0 ∈ A.toSetValued (u + v) := A.map_add_superset u v hsum
    simpa using hmem
  · intro hv
    change ∀ u, A.toSetValued u ⊆ A.toSetValued (u + v) at hv
    change (0 : Fin n → ℝ) ∈ A.toSetValued v
    -- Evaluate the shift-invariance condition at the origin.
    have hmem : (0 : Fin n → ℝ) ∈ A.toSetValued ((0 : Fin m → ℝ) + v) := hv 0 A.zero_mem
    simpa using hmem

/-- Proposition 39.0.2: Let `A : ℝ^m ⇉ ℝ^n` be a convex process. Then:

(i) `A u` is convex for every `u`.

(ii) `A 0` is a convex cone containing the origin, and
`A 0 = { y | A u + y ⊆ A u, ∀ u }`.

(iii) `dom A := { u | A u ≠ ∅ }` and `range A := ⋃ u, A u` are convex cones containing the origin.

(iv) `A⁻¹` is a convex process and `dom (A⁻¹) = range A`, `range (A⁻¹) = dom A`.

(v) `A⁻¹ 0 = { v | A (u + v) ⊇ A u, ∀ u }`. -/
theorem convexProcess_prop_39_0_2 {m n : ℕ} (A : ConvexProcess m n) :
    (∀ u, Convex ℝ (A.toSetValued u)) ∧
      ((∃ C : ConvexCone ℝ (Fin n → ℝ), (C : Set _) = A.toSetValued 0) ∧
        (0 : (Fin n → ℝ)) ∈ A.toSetValued 0 ∧
        A.toSetValued 0 =
          { y | ∀ u, A.toSetValued u + ({y} : Set (Fin n → ℝ)) ⊆ A.toSetValued u }) ∧
      ((∃ C : ConvexCone ℝ (Fin m → ℝ), (C : Set _) = A.dom) ∧
        (0 : (Fin m → ℝ)) ∈ A.dom ∧
        (∃ C : ConvexCone ℝ (Fin n → ℝ), (C : Set _) = A.range) ∧
        (0 : (Fin n → ℝ)) ∈ A.range) ∧
      ((∃ Ainv : ConvexProcess n m, Ainv.toSetValued = A.inverseMap) ∧
        setValuedDom A.inverseMap = A.range ∧
        setValuedRange A.inverseMap = A.dom) ∧
      (A.inverseMap (0 : (Fin n → ℝ)) =
        { v | ∀ u, A.toSetValued u ⊆ A.toSetValued (u + v) }) :=
  by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u
    -- Convexity follows from the explicit fiber-combination lemma.
    rw [convex_iff_add_mem]
    intro x₁ hx₁ x₂ hx₂ a b ha hb hab
    have ha_le_one : a ≤ 1 := by linarith
    have hab' : 1 - a = b := by linarith
    simpa [hab'] using
      (helperForProposition_39_0_2_fiber_combo_mem A (u := u) (x₁ := x₁) (x₂ := x₂)
        (t := a) hx₁ hx₂ ⟨ha, ha_le_one⟩)
  · -- Part (ii) is packaged in the dedicated zero-fiber helper.
    rcases helperForProposition_39_0_2_zeroFiber_cone_and_stability A with
      ⟨⟨hcone, hzero⟩, hstable⟩
    exact ⟨hcone, hzero, hstable⟩
  · -- Part (iii) is packaged in the dedicated domain/range helper.
    rcases helperForProposition_39_0_2_dom_range_cones A with
      ⟨⟨hdomCone, hdomZero⟩, hrange⟩
    rcases hrange with ⟨hrangeCone, hrangeZero⟩
    exact ⟨hdomCone, hdomZero, hrangeCone, hrangeZero⟩
  · -- Part (iv) is packaged in the dedicated inverse-process helper.
    exact helperForProposition_39_0_2_inverseProcess_and_dom_range A
  · -- Part (v) is the inverse-zero characterization helper.
    exact helperForProposition_39_0_2_inverse_zero_eq_shiftInvariant A

-- Proof sketch: Use Proposition 39.0.2(ii) to control the recession cone `A 0`; boundedness forces
-- `A 0` to be `{0}`. Then positive homogeneity and superadditivity upgrade to additivity, giving a
-- single-valued additive and (full) homogeneous mapping `u ↦ y(u)`. Show the graph is a linear
-- subspace, hence the mapping is represented by a linear map `f`, with `A u = {f u}`.
/-- Helper for Theorem 39.1: boundedness forces the zero fiber of the process to collapse to the
singleton `{0}`. -/
lemma helperForTheorem_39_1_zeroFiber_eq_singleton_zero {m n : ℕ} (A : ConvexProcess m n)
    (hA0 : Bornology.IsBounded (A.toSetValued (0 : Fin m → ℝ))) :
    A.toSetValued (0 : Fin m → ℝ) = ({0} : Set (Fin n → ℝ)) := by
  rcases convexProcess_prop_39_0_2 A with ⟨_, hzeroFiber, _, _, _⟩
  rcases hzeroFiber with ⟨⟨C, hC⟩, _, _⟩
  obtain ⟨R, hR⟩ := hA0.exists_norm_le
  have hR_nonneg : 0 ≤ R := by
    have : ‖(0 : Fin n → ℝ)‖ ≤ R := hR 0 A.zero_mem
    simpa using this
  ext y
  constructor
  · intro hy
    by_cases hy0 : y = 0
    · -- The zero vector is the only possible bounded cone direction.
      simpa [hy0]
    · have hyC : y ∈ C := by
        change y ∈ (C : Set (Fin n → ℝ))
        rw [hC]
        exact hy
      have hy_norm_pos : 0 < ‖y‖ := by
        exact norm_pos_iff.2 hy0
      have hy_norm_ne : ‖y‖ ≠ 0 := ne_of_gt hy_norm_pos
      let r : ℝ := (R + 1) / ‖y‖
      have hr : 0 < r := by
        dsimp [r]
        exact div_pos (by linarith) hy_norm_pos
      -- Scale `y` along the cone and compare the resulting norm with the boundedness constant.
      have hscaledC : r • y ∈ C := C.smul_mem hr hyC
      have hscaled : r • y ∈ A.toSetValued (0 : Fin m → ℝ) := by
        change r • y ∈ (C : Set (Fin n → ℝ)) at hscaledC
        rw [← hC]
        exact hscaledC
      have hbound : ‖r • y‖ ≤ R := hR (r • y) hscaled
      have hnorm : ‖r • y‖ = R + 1 := by
        calc
          ‖r • y‖ = |r| * ‖y‖ := norm_smul r y
          _ = r * ‖y‖ := by rw [abs_of_pos hr]
          _ = R + 1 := by
            dsimp [r]
            rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hy_norm_ne, mul_one]
      have : R + 1 ≤ R := by simpa [hnorm] using hbound
      linarith
  · intro hy
    have hy0 : y = 0 := by simpa using hy
    simpa [hy0] using A.zero_mem

/-- Helper for Theorem 39.1: once the zero fiber is `{0}`, every fiber contains a unique point. -/
lemma helperForTheorem_39_1_existsUniqueMem_fiber_of_dom_univ {m n : ℕ}
    (A : ConvexProcess m n) (hdom : A.dom = Set.univ)
    (hzero : A.toSetValued (0 : Fin m → ℝ) = ({0} : Set (Fin n → ℝ))) :
    ∀ u, ∃! x : Fin n → ℝ, x ∈ A.toSetValued u := by
  intro u
  have hu_dom : u ∈ A.dom := by
    rw [hdom]
    simp
  change (A.toSetValued u).Nonempty at hu_dom
  rcases hu_dom with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro x₁ hx₁
  have hneg_dom : -u ∈ A.dom := by
    rw [hdom]
    simp
  change (A.toSetValued (-u)).Nonempty at hneg_dom
  rcases hneg_dom with ⟨y, hy⟩
  -- Translate both fiber points by the same element of `A (-u)` to land in the zero fiber.
  have hx_sum : x + y ∈ A.toSetValued (0 : Fin m → ℝ) := by
    have hsum : x + y ∈ A.toSetValued u + A.toSetValued (-u) :=
      Set.mem_add.2 ⟨x, hx, y, hy, rfl⟩
    have hmem : x + y ∈ A.toSetValued (u + -u) := A.map_add_superset u (-u) hsum
    simpa using hmem
  have hx₁_sum : x₁ + y ∈ A.toSetValued (0 : Fin m → ℝ) := by
    have hsum : x₁ + y ∈ A.toSetValued u + A.toSetValued (-u) :=
      Set.mem_add.2 ⟨x₁, hx₁, y, hy, rfl⟩
    have hmem : x₁ + y ∈ A.toSetValued (u + -u) := A.map_add_superset u (-u) hsum
    simpa using hmem
  have hx_eq_neg : x = -y := by
    have hx_zero : x + y = 0 := by
      have : x + y ∈ ({0} : Set (Fin n → ℝ)) := by simpa [hzero] using hx_sum
      simpa using this
    exact eq_neg_of_add_eq_zero_left hx_zero
  have hx₁_eq_neg : x₁ = -y := by
    have hx₁_zero : x₁ + y = 0 := by
      have : x₁ + y ∈ ({0} : Set (Fin n → ℝ)) := by simpa [hzero] using hx₁_sum
      simpa using this
    exact eq_neg_of_add_eq_zero_left hx₁_zero
  exact hx₁_eq_neg.trans hx_eq_neg.symm

/-- Helper for Theorem 39.1: the chosen representative of each unique fiber exactly recovers that
fiber as a singleton. -/
lemma helperForTheorem_39_1_chosenFiber_eq_singleton {m n : ℕ}
    (A : ConvexProcess m n) (hex : ∀ u, ∃! x : Fin n → ℝ, x ∈ A.toSetValued u) :
    let g : (Fin m → ℝ) → (Fin n → ℝ) := fun u => Classical.choose (hex u)
    ∀ u, A.toSetValued u = ({g u} : Set (Fin n → ℝ)) := by
  classical
  intro g u
  ext x
  constructor
  · intro hx
    -- Uniqueness in the fiber identifies every point with the chosen representative.
    have hx_eq : x = g u := (Classical.choose_spec (hex u)).2 x hx
    simpa [hx_eq]
  · intro hx
    -- The chosen representative belongs to the fiber by construction.
    have hg_mem : g u ∈ A.toSetValued u := (Classical.choose_spec (hex u)).1
    have hx_eq : x = g u := by simpa using hx
    simpa [hx_eq] using hg_mem

/-- Helper for Theorem 39.1: once every fiber is a singleton, the chosen representative map is
additive and sends `0` to `0`. -/
lemma helperForTheorem_39_1_chosenMap_add {m n : ℕ} (A : ConvexProcess m n)
    (g : (Fin m → ℝ) → (Fin n → ℝ))
    (hgset : ∀ u, A.toSetValued u = ({g u} : Set (Fin n → ℝ))) :
    g (0 : Fin m → ℝ) = 0 ∧ ∀ u₁ u₂, g (u₁ + u₂) = g u₁ + g u₂ := by
  have hg_zero : g (0 : Fin m → ℝ) = 0 := by
    -- The distinguished point in the zero fiber must be the origin.
    have hzero_mem : (0 : Fin n → ℝ) ∈ ({g (0 : Fin m → ℝ)} : Set (Fin n → ℝ)) := by
      simpa [hgset (0 : Fin m → ℝ)] using A.zero_mem
    have hzero_eq : (0 : Fin n → ℝ) = g (0 : Fin m → ℝ) := by
      simpa using hzero_mem
    exact hzero_eq.symm
  refine ⟨hg_zero, ?_⟩
  intro u₁ u₂
  -- Superadditivity puts the sum of the chosen fiber points into the singleton fiber over `u₁+u₂`.
  have hg₁ : g u₁ ∈ A.toSetValued u₁ := by
    simpa [hgset u₁] using (show g u₁ ∈ ({g u₁} : Set (Fin n → ℝ)) by simp)
  have hg₂ : g u₂ ∈ A.toSetValued u₂ := by
    simpa [hgset u₂] using (show g u₂ ∈ ({g u₂} : Set (Fin n → ℝ)) by simp)
  have hsum : g u₁ + g u₂ ∈ A.toSetValued u₁ + A.toSetValued u₂ :=
    Set.mem_add.2 ⟨g u₁, hg₁, g u₂, hg₂, rfl⟩
  have hmem : g u₁ + g u₂ ∈ A.toSetValued (u₁ + u₂) := A.map_add_superset u₁ u₂ hsum
  have hadd_eq : g u₁ + g u₂ = g (u₁ + u₂) := by
    simpa [hgset (u₁ + u₂)] using hmem
  exact hadd_eq.symm

/-- Helper for Theorem 39.1: the chosen singleton representative is homogeneous for every real
scalar, not just positive scalars. -/
lemma helperForTheorem_39_1_chosenMap_smul {m n : ℕ} (A : ConvexProcess m n)
    (g : (Fin m → ℝ) → (Fin n → ℝ))
    (hgset : ∀ u, A.toSetValued u = ({g u} : Set (Fin n → ℝ)))
    (hzero : g (0 : Fin m → ℝ) = 0)
    (hadd : ∀ u₁ u₂, g (u₁ + u₂) = g u₁ + g u₂) :
    ∀ (r : ℝ) (u : Fin m → ℝ), g (r • u) = r • g u := by
  have hsmul_pos : ∀ ⦃r : ℝ⦄, 0 < r → ∀ u, g (r • u) = r • g u := by
    intro r hr u
    -- Positive homogeneity of the process turns into equality because the target fiber is a singleton.
    have hg_mem : g u ∈ A.toSetValued u := by
      simpa [hgset u] using (show g u ∈ ({g u} : Set (Fin n → ℝ)) by simp)
    have hscaled : r • g u ∈ A.toSetValued (r • u) := by
      have hscaled_mem : r • g u ∈ r • A.toSetValued u := Set.mem_smul_set.2 ⟨g u, hg_mem, rfl⟩
      simpa [A.map_smul_pos u r hr] using hscaled_mem
    have hscaled_eq : r • g u = g (r • u) := by
      simpa [hgset (r • u)] using hscaled
    exact hscaled_eq.symm
  have hneg : ∀ u, g (-u) = -g u := by
    intro u
    -- Additivity at `(-u,u)` identifies the chosen point in `A (-u)` as the additive inverse.
    have hsum : g (-u) + g u = 0 := by
      have hsum' : g ((-u) + u) = g (-u) + g u := hadd (-u) u
      simpa [hzero] using hsum'.symm
    exact eq_neg_of_add_eq_zero_left hsum
  intro r u
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · -- Route correction: positive homogeneity only applies for `r > 0`, so the negative case is
    -- reduced to the positive case on `-r` together with `g (-u) = - g u`.
    have hneg_r : 0 < -r := by linarith
    calc
      g (r • u) = g ((-r) • (-u)) := by simp
      _ = (-r) • g (-u) := hsmul_pos hneg_r (-u)
      _ = r • g u := by rw [hneg u]; simp
  · -- At the zero scalar, the homogeneity statement is exactly `g 0 = 0`.
    simpa [hzero]
  · exact hsmul_pos hr u

/-- Theorem 39.1: If `A` is a convex process from `ℝ^m` to `ℝ^n` such that `dom A = ℝ^m` and `A 0`
is bounded, then `A` is a linear transformation (i.e. it is single-valued and given by a linear
map). -/
theorem ConvexProcess.exists_linearMap_of_dom_univ_of_bounded_zero {m n : ℕ} (A : ConvexProcess m n)
    (hdom : A.dom = Set.univ) (hA0 : Bornology.IsBounded (A.toSetValued 0)) :
    ∃ f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∀ u, A.toSetValued u = ({f u} : Set (Fin n → ℝ)) :=
  by
  classical
  -- First collapse the zero fiber using boundedness and the cone structure from Proposition 39.0.2.
  have hzero :
      A.toSetValued (0 : Fin m → ℝ) = ({0} : Set (Fin n → ℝ)) :=
    helperForTheorem_39_1_zeroFiber_eq_singleton_zero A hA0
  -- Then every fiber becomes a singleton because translating by a point of `A (-u)` lands in `A 0`.
  have hex :
      ∀ u, ∃! x : Fin n → ℝ, x ∈ A.toSetValued u :=
    helperForTheorem_39_1_existsUniqueMem_fiber_of_dom_univ A hdom hzero
  let g : (Fin m → ℝ) → (Fin n → ℝ) := fun u => Classical.choose (hex u)
  have hgset : ∀ u, A.toSetValued u = ({g u} : Set (Fin n → ℝ)) := by
    simpa [g] using helperForTheorem_39_1_chosenFiber_eq_singleton A hex
  -- Finally, superadditivity and positive homogeneity force the chosen representative map to be linear.
  rcases helperForTheorem_39_1_chosenMap_add A g hgset with ⟨hg_zero, hg_add⟩
  have hg_smul : ∀ (r : ℝ) (u : Fin m → ℝ), g (r • u) = r • g u :=
    helperForTheorem_39_1_chosenMap_smul A g hgset hg_zero hg_add
  let f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := {
    toFun := g
    map_add' := hg_add
    map_smul' := hg_smul
  }
  refine ⟨f, ?_⟩
  simpa [f] using hgset

/-- The set-valued mapping `A` from Example 39.0.3, packaged as a set-valued function:
`x ∈ A u` iff `u ≥ 0` and `x ≤ B u` (componentwise). -/
def linearLowerSetValued {m n : ℕ} (B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (Fin m → ℝ) → Set (Fin n → ℝ) :=
  fun u => { x | 0 ≤ u ∧ x ≤ B u }

/-- Helper for Example 39.0.3: a positive scalar can be cancelled from a pointwise
nonnegativity condition on `Fin m → ℝ`. -/
lemma helperForExample_39_0_3_nonneg_of_pos_smul_nonneg {m : ℕ} {r : ℝ} {u : Fin m → ℝ}
    (hr : 0 < r) (hu : 0 ≤ r • u) : 0 ≤ u := by
  -- Check each coordinate and divide by the positive scalar using real arithmetic.
  intro i
  change 0 ≤ u i
  have hu_i : 0 ≤ (r • u) i := hu i
  change 0 ≤ r * u i at hu_i
  nlinarith

/-- Helper for Example 39.0.3: the lower-set fibers are superadditive because both
the nonnegative orthant and the order bound are stable under addition. -/
lemma helperForExample_39_0_3_map_add_superset {m n : ℕ}
    (B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (u₁ u₂ : Fin m → ℝ) :
    linearLowerSetValued B u₁ + linearLowerSetValued B u₂ ⊆
      linearLowerSetValued B (u₁ + u₂) := by
  -- Unpack a Minkowski-sum witness and add the two coordinatewise bounds.
  intro x hx
  rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  refine ⟨add_nonneg hx₁.1 hx₂.1, ?_⟩
  simpa [linearLowerSetValued, LinearMap.map_add] using add_le_add hx₁.2 hx₂.2

/-- Helper for Example 39.0.3: positive homogeneity of the lower-set fibers follows by
scaling both the input nonnegativity condition and the upper bound `x ≤ B u`. -/
lemma helperForExample_39_0_3_map_smul_pos {m n : ℕ}
    (B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (u : Fin m → ℝ) (r : ℝ) (hr : 0 < r) :
    linearLowerSetValued B (r • u) = r • linearLowerSetValued B u := by
  -- Compare the two sets fiberwise and scale/descale each coordinate inequality.
  ext x
  constructor
  · intro hx
    refine Set.mem_smul_set.2 ?_
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · refine ⟨helperForExample_39_0_3_nonneg_of_pos_smul_nonneg hr hx.1, ?_⟩
      -- Descale the upper bound `x ≤ B (r • u)` back to `r⁻¹ • x ≤ B u`.
      intro i
      change r⁻¹ * x i ≤ B u i
      have hxi : x i ≤ B (r • u) i := hx.2 i
      have hscaled : r⁻¹ * x i ≤ r⁻¹ * B (r • u) i :=
        mul_le_mul_of_nonneg_left hxi (inv_nonneg.mpr hr.le)
      calc
        r⁻¹ * x i ≤ r⁻¹ * B (r • u) i := hscaled
        _ = B u i := by
          have hmap_i : B (r • u) i = r * B u i := by
            change B (r • u) i = (r • B u) i
            exact congrArg (fun z => z i) (B.map_smul r u)
          rw [hmap_i]
          field_simp [hr.ne']
    · -- The witness really rescales back to the original point `x`.
      ext i
      change r * (r⁻¹ * x i) = x i
      field_simp [hr.ne']
  · intro hx
    rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
    refine ⟨smul_nonneg hr.le hy.1, ?_⟩
    -- Scale the pointwise upper bound `y ≤ B u` and rewrite `B (r • u)`.
    intro i
    have hyi : y i ≤ B u i := hy.2 i
    have hscaled : r * y i ≤ r * B u i := by
      nlinarith
    have hmap_i : r * B u i = B (r • u) i := by
      change (r • B u) i = B (r • u) i
      exact (congrArg (fun z => z i) (B.map_smul r u)).symm
    exact hscaled.trans_eq hmap_i

/-- Helper for Example 39.0.3: the inverse fiber is exactly the set of nonnegative
inputs whose image under `B` dominates the target point. -/
lemma helperForExample_39_0_3_inverse_eq {m n : ℕ}
    (B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (x : Fin n → ℝ) :
    setValuedInverse (linearLowerSetValued B) x = { u | 0 ≤ u ∧ B u ≥ x } := by
  -- Unfolding the inverse leaves the same fiber condition, just written in reverse order.
  ext u
  rfl

/-- Helper for Example 39.0.3: the origin belongs to the fiber over the origin because
both the nonnegativity and order constraints become reflexive after rewriting `B 0 = 0`. -/
lemma helperForExample_39_0_3_zero_mem {m n : ℕ}
    (B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (0 : Fin n → ℝ) ∈ linearLowerSetValued B (0 : Fin m → ℝ) := by
  -- At the origin, the defining inequalities of the lower-set fiber are immediate.
  refine ⟨le_rfl, ?_⟩
  simp [LinearMap.map_zero]

-- Proof sketch: Either check axioms (a), (b), (c) of `ConvexProcess` directly from linearity of `B`
-- and the order properties of `≤` on `Fin _ → ℝ`, or use Proposition 39.0.1 by identifying the
-- graph as an intersection of a linear subspace with the product of the nonnegative orthant and a
-- lower set, hence a convex cone; the inverse formula is then a direct unpacking of membership.
/-- Example 39.0.3: Let `B : ℝ^m →ₗ[ℝ] ℝ^n` be linear (with componentwise order). Define the
set-valued mapping `A` by `A u = {x | x ≤ B u}` for `u ≥ 0`, and `A u = ∅` otherwise. Then `A` is a
convex process, and its inverse satisfies `A⁻¹ x = {u | u ≥ 0 ∧ B u ≥ x}`. -/
theorem example_39_0_3 {m n : ℕ} (B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (∃ cp : ConvexProcess m n, cp.toSetValued = linearLowerSetValued B) ∧
      ∀ x, setValuedInverse (linearLowerSetValued B) x =
        { u | 0 ≤ u ∧ B u ≥ x } :=
  by
  refine ⟨?_, ?_⟩
  · -- Package the direct fiberwise addition, scaling, and origin checks into a convex process.
    refine ⟨{
      toSetValued := linearLowerSetValued B
      map_add_superset := helperForExample_39_0_3_map_add_superset B
      map_smul_pos := helperForExample_39_0_3_map_smul_pos B
      zero_mem := helperForExample_39_0_3_zero_mem B
    }, rfl⟩
  · -- The inverse formula is exactly the defining membership condition of the fibers.
    intro x
    exact helperForExample_39_0_3_inverse_eq B x

/-- A convex cone is polyhedral if it can be described by finitely many linear inequalities
(an `H`-representation): there are finitely many linear functionals `φ i` such that
`x ∈ C` iff `0 ≤ φ i x` for all `i`. -/
def ConvexCone.IsPolyhedral {V : Type*} [AddCommGroup V] [Module ℝ V] (C : ConvexCone ℝ V) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (φ : ι → V →ₗ[ℝ] ℝ),
    (C : Set V) = { x | ∀ i, 0 ≤ φ i x }

namespace ConvexProcess

/-- Definition 39.0.4: A convex process `A` is polyhedral if `graph A` is a polyhedral convex cone. -/
def IsPolyhedral {m n : ℕ} (A : ConvexProcess m n) : Prop :=
  ∃ C : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)),
    (C : Set _) = setValuedGraph A.toSetValued ∧ C.IsPolyhedral

-- Proof sketch: By Proposition 39.0.1, convex processes correspond to convex cones in
-- `ℝ^(m+n)` containing the origin. The topological closure of such a cone is again a convex cone
-- containing the origin, so the correspondence yields a convex process with graph
-- `closure (graph A)`.
/-- A convex process whose graph is the closure of the graph of `A` exists. -/
theorem exists_closureProcess {m n : ℕ} (A : ConvexProcess m n) :
    ∃ B : ConvexProcess m n,
      setValuedGraph B.toSetValued = closure (setValuedGraph A.toSetValued) :=
  by
  let Aclosure : (Fin m → ℝ) → Set (Fin n → ℝ) :=
    fun u => { x | (u, x) ∈ closure (setValuedGraph A.toSetValued) }
  -- The graph of `A` is a convex cone, so its closure is again a convex cone.
  rcases (convexProcess_iff_graph_isConvexCone A.toSetValued).1 ⟨A, rfl⟩ with
    ⟨⟨C, hC⟩, hzero⟩
  have hCclosure :
      ((C.closure : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ))) : Set
        ((Fin m → ℝ) × (Fin n → ℝ))) =
        closure (setValuedGraph A.toSetValued) := by
    rw [ConvexCone.coe_closure, hC]
  have hAclosure_graph : setValuedGraph Aclosure = closure (setValuedGraph A.toSetValued) := by
    ext p
    rfl
  have hgraph :
      ((C.closure : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ))) : Set
        ((Fin m → ℝ) × (Fin n → ℝ))) = setValuedGraph Aclosure := by
    rw [hCclosure, hAclosure_graph]
  have hzero_closure :
      (0 : ((Fin m → ℝ) × (Fin n → ℝ))) ∈ setValuedGraph Aclosure := by
    rw [hAclosure_graph]
    exact subset_closure hzero
  rcases helperForProposition_39_0_1_exists_convexProcess_ofGraphCone
      Aclosure C.closure hgraph hzero_closure with ⟨B, hB⟩
  refine ⟨B, ?_⟩
  rw [hB, hAclosure_graph]

/-- Definition 39.0.5: The closure of a convex process `A` is the convex process `cl A` whose graph
is `closure (graph A)`. -/
noncomputable def cl {m n : ℕ} (A : ConvexProcess m n) : ConvexProcess m n :=
  Classical.choose (exists_closureProcess A)

/-- A convex process `A` is closed if `cl A = A`. -/
def IsClosed {m n : ℕ} (A : ConvexProcess m n) : Prop :=
  A.cl = A

end ConvexProcess

end Section39
end Chap08

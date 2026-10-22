/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open MeasureTheory MeasurableSpace Set
open scoped MeasureTheory

/-! ### Example 1.11

Support API for the standard set-family examples from Section 1.1. The
source-facing item claims are stated below, while the remaining declarations are
auxiliary bridges and helper facts used to keep the formalization close to the
textbook families.
-/

/-- The two-set family consisting only of `∅` and the whole space. -/
def trivialTwoSetFamily (Ω : Type u) : Set (Set Ω) :=
  {∅, univ}

/-- The family consisting only of the empty set. -/
def emptySetFamily (Ω : Type u) : Set (Set Ω) :=
  ({∅} : Set (Set Ω))

/-- The family of countable subsets of `ℝ`. -/
def countableSubsetFamily : Set (Set ℝ) :=
  {s : Set ℝ | s.Countable}

/-- The family of right-closed bounded intervals `(a, b]` in `ℝ`. -/
def rightClosedIntervalFamily : Set (Set ℝ) :=
  {s : Set ℝ | ∃ a b : ℝ, a ≤ b ∧ s = Ioc a b}

/-- The family of finite unions of bounded intervals in `ℝ`, expressed as finite unions of bounded
order-connected sets. -/
def finiteUnionBoundedIntervalFamily : Set (Set ℝ) :=
  {s : Set ℝ |
    ∃ S : Finset (Set ℝ),
      (∀ t ∈ S, t.OrdConnected ∧ BddBelow t ∧ BddAbove t) ∧
        s = ⋃₀ (↑S : Set (Set ℝ))}

/-- The family of finite unions of arbitrary intervals in `ℝ`, expressed as finite unions of
order-connected sets. -/
def finiteUnionIntervalFamily : Set (Set ℝ) :=
  {s : Set ℝ |
    ∃ S : Finset (Set ℝ),
      (∀ t ∈ S, t.OrdConnected) ∧ s = ⋃₀ (↑S : Set (Set ℝ))}

/-- The family `A = ⋃ n, A_n` used in the sequence-cylinder example, where
`A₀ = {∅}` and `A_{n+1}` consists of the cylinders determined by the first
`n + 1` coordinates. -/
def sequenceCylinderFamily (E : Type u) : Set (Set (ℕ → E)) :=
  {s : Set (ℕ → E) |
    s = ∅ ∨
      ∃ n : ℕ, ∃ x : Fin (n + 1) → E, s = {ω | ∀ i : Fin (n + 1), ω i = x i}}

/-- The textbook level family `A_n` for the sequence-cylinder example. -/
def sequenceCylinderLevel (E : Type u) : ℕ → Set (Set (ℕ → E))
  | 0 => ({∅} : Set (Set (ℕ → E)))
  | n + 1 => {s : Set (ℕ → E) | ∃ x : Fin (n + 1) → E, s = {ω | ∀ i : Fin (n + 1), ω i = x i}}

/-- `A₀` is exactly `{∅}` in the notation for the sequence-cylinder example. -/
lemma mem_sequenceCylinderLevel_zero {E : Type u} {s : Set (ℕ → E)} :
    s ∈ sequenceCylinderLevel E 0 ↔ s = ∅ := by
  simp [sequenceCylinderLevel]

/-- For `n + 1`, membership in `A_{n+1}` means being the cylinder determined by
some prefix of length `n + 1`. -/
lemma mem_sequenceCylinderLevel_succ_iff {E : Type u} {n : ℕ} {s : Set (ℕ → E)} :
    s ∈ sequenceCylinderLevel E (n + 1) ↔
      ∃ x : Fin (n + 1) → E, s = {ω | ∀ i : Fin (n + 1), ω i = x i} := by
  rfl

/-- The helper encoding `sequenceCylinderFamily` is exactly the textbook union
`A = ⋃ n, A_n`. -/
lemma sequenceCylinderFamily_eq_iUnion_sequenceCylinderLevel (E : Type u) :
    sequenceCylinderFamily E = ⋃ n, sequenceCylinderLevel E n := by
  ext s
  constructor
  · intro hs
    rcases hs with rfl | ⟨n, x, rfl⟩
    · exact Set.mem_iUnion.mpr ⟨0, by simp [sequenceCylinderLevel]⟩
    · exact Set.mem_iUnion.mpr ⟨n + 1, by exact ⟨x, rfl⟩⟩
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨n, hn⟩
    cases n with
    | zero =>
        left
        simpa [sequenceCylinderLevel] using hn
    | succ n =>
        right
        exact ⟨n, by simpa [sequenceCylinderLevel] using hn⟩

/-- The family of finite or cofinite subsets of `Ω`. -/
def finiteOrCofiniteFamily (Ω : Type u) : Set (Set Ω) :=
  {s : Set Ω | s.Finite ∨ sᶜ.Finite}

/-- The family of countable or cocountable subsets of `Ω`. -/
def countableOrCocountableFamily (Ω : Type u) : Set (Set Ω) :=
  {s : Set Ω | s.Countable ∨ sᶜ.Countable}

/-- The explicit six-set family on the four-point space `Fin 4`, corresponding to the textbook
example on `{1,2,3,4}` up to relabeling. -/
def fourPointLambdaFamily : Set (Set (Fin 4)) :=
  {∅, ({0, 1} : Set (Fin 4)), ({0, 3} : Set (Fin 4)), ({1, 2} : Set (Fin 4)),
    ({2, 3} : Set (Fin 4)), (univ : Set (Fin 4))}

/-- A family of sets is a lambda-system if it is the underlying family of a Dynkin system. -/
def IsSetLambdaSystem {Ω : Type u} (A : Set (Set Ω)) : Prop :=
  ∃ d : DynkinSystem Ω, d.Has = A

/-- A family of sets is a sigma-algebra if it is the family of measurable sets of a measurable
space. -/
def IsSetSigmaAlgebra {Ω : Type u} (A : Set (Set Ω)) : Prop :=
  ∃ m : MeasurableSpace Ω, {s : Set Ω | MeasurableSet[m] s} = A

-- Semantic recall: mathlib already exposes the half-open interval semiring via
-- `MeasureTheory.IsSetSemiring.Ioc`; this file packages the textbook item as
-- atomic source-facing theorems and support API.

/-- Helper: if a family already occurs as the measurable sets of some measurable
space, then the sigma-algebra generated from that family adds no new sets. -/
lemma generatedSigma_eq_of_existsMeasurableSpace {Ω : Type u} {A : Set (Set Ω)}
    (hA : ∃ m : MeasurableSpace Ω, {s : Set Ω | MeasurableSet[m] s} = A) :
    {s : Set Ω | MeasurableSet[generateFrom A] s} = A := by
  rcases hA with ⟨m, hm⟩
  ext s
  constructor
  · -- Push generated measurability along the least-property map `generateFrom A ≤ m`.
    intro hs
    have hle : generateFrom A ≤ m := by
      refine MeasurableSpace.generateFrom_le ?_
      intro t ht
      have hm_t : MeasurableSet[m] t ↔ t ∈ A := by
        simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ t ∈ S) hm
      exact hm_t.mpr ht
    have hs' : MeasurableSet[m] s := hle s hs
    have hm_s : MeasurableSet[m] s ↔ s ∈ A := by
      simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ s ∈ S) hm
    exact hm_s.mp hs'
  · -- Every set already measurable in `m` is one of the generators of `generateFrom A`.
    intro hs
    exact MeasurableSpace.measurableSet_generateFrom hs

/-- Helper: if a family already occurs as the measurable sets of some measurable
space, then the Dynkin system generated from that family adds no new sets. -/
lemma generatedDynkin_eq_of_existsMeasurableSpace {Ω : Type u} {A : Set (Set Ω)}
    (hA : ∃ m : MeasurableSpace Ω, {s : Set Ω | MeasurableSet[m] s} = A) :
    {s : Set Ω | (DynkinSystem.generate A).Has s} = A := by
  rcases hA with ⟨m, hm⟩
  have hpi : IsPiSystem A := by
    intro s hs t ht hst
    have hs' : MeasurableSet[m] s := by
      have hm_s : MeasurableSet[m] s ↔ s ∈ A := by
        simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ s ∈ S) hm
      exact hm_s.mpr hs
    have ht' : MeasurableSet[m] t := by
      have hm_t : MeasurableSet[m] t ↔ t ∈ A := by
        simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ t ∈ S) hm
      exact hm_t.mpr ht
    have hm_st : MeasurableSet[m] (s ∩ t) ↔ s ∩ t ∈ A := by
      simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ s ∩ t ∈ S) hm
    exact hm_st.mp (hs'.inter ht')
  have hSigma : {s : Set Ω | MeasurableSet[generateFrom A] s} = A :=
    generatedSigma_eq_of_existsMeasurableSpace ⟨m, hm⟩
  have hDynkin : DynkinSystem.ofMeasurableSpace (generateFrom A) = DynkinSystem.generate A := by
    simpa [DynkinSystem.ofMeasurableSpace_toMeasurableSpace] using
      congrArg DynkinSystem.ofMeasurableSpace (DynkinSystem.generateFrom_eq hpi)
  ext s
  constructor
  · -- Rewrite generated-Dynkin membership back to measurability in `generateFrom A`.
    intro hs
    have hDynkin_s : MeasurableSet[generateFrom A] s ↔ (DynkinSystem.generate A).Has s := by
      simpa [Set.mem_setOf_eq] using congrArg (fun d : DynkinSystem Ω ↦ d.Has s) hDynkin
    have hSigma_s : MeasurableSet[generateFrom A] s ↔ s ∈ A := by
      simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ s ∈ S) hSigma
    exact hSigma_s.mp (hDynkin_s.mpr hs)
  · -- The generated Dynkin system contains every set measurable in `generateFrom A`.
    intro hs
    have hDynkin_s : MeasurableSet[generateFrom A] s ↔ (DynkinSystem.generate A).Has s := by
      simpa [Set.mem_setOf_eq] using congrArg (fun d : DynkinSystem Ω ↦ d.Has s) hDynkin
    have hSigma_s : MeasurableSet[generateFrom A] s ↔ s ∈ A := by
      simpa [Set.mem_setOf_eq] using congrArg (fun S : Set (Set Ω) ↦ s ∈ S) hSigma
    exact hDynkin_s.mp (hSigma_s.mpr hs)

-- Proof sketch: realize `{∅, Ω}` as the measurable sets of a specific measurable space.
/-- Helper for item (i): realize `{∅, Ω}` as the measurable sets of a measurable space. -/
theorem trivialTwoSetFamily_exists_measurableSpace (Ω : Type u) [Nonempty Ω] :
    ∃ m : MeasurableSpace Ω, {s : Set Ω | MeasurableSet[m] s} = trivialTwoSetFamily Ω := by
  -- The bottom measurable space has exactly `∅` and `univ` as measurable sets.
  refine ⟨⊥, ?_⟩
  ext s
  simpa [trivialTwoSetFamily] using
    (MeasurableSpace.measurableSet_bot_iff :
      MeasurableSet[(⊥ : MeasurableSpace Ω)] s ↔ s = ∅ ∨ s = Set.univ)

-- Proof sketch: the measurable-space description of `{∅, Ω}` yields the algebra structure
-- immediately.
/-- Part of Example 1.11 (1): On a nonempty space, the family `{∅, Ω}` is an algebra of sets. -/
theorem trivialTwoSetFamily_isSetAlgebra (Ω : Type u) [Nonempty Ω] :
    IsSetAlgebra (trivialTwoSetFamily Ω) := by
  refine
    { empty_mem := by simp [trivialTwoSetFamily]
      compl_mem := ?_
      union_mem := ?_ }
  · -- Complements swap the two members of the family.
    intro s hs
    have hs' : s = ∅ ∨ s = univ := by
      simpa [trivialTwoSetFamily] using hs
    rcases hs' with rfl | rfl <;> simp [trivialTwoSetFamily]
  · -- Unions of the only two possible members stay inside the same two-point family.
    intro s t hs ht
    have hs' : s = ∅ ∨ s = univ := by
      simpa [trivialTwoSetFamily] using hs
    have ht' : t = ∅ ∨ t = univ := by
      simpa [trivialTwoSetFamily] using ht
    rcases hs' with rfl | rfl <;> rcases ht' with rfl | rfl <;>
      simp [trivialTwoSetFamily]

-- Proof sketch: realize `{∅, Ω}` as the underlying family of a Dynkin system.
/-- Part of Example 1.11 (2): On a nonempty space, the family `{∅, Ω}` is a lambda-system. -/
theorem trivialTwoSetFamily_isSetLambdaSystem (Ω : Type u) [Nonempty Ω] :
    IsSetLambdaSystem (trivialTwoSetFamily Ω) := by
  refine ⟨DynkinSystem.generate (trivialTwoSetFamily Ω), ?_⟩
  simpa using
    generatedDynkin_eq_of_existsMeasurableSpace (trivialTwoSetFamily_exists_measurableSpace Ω)

-- Proof sketch: reuse the explicit measurable-space realization of `{∅, Ω}`.
/-- Part of Example 1.11 (3): On a nonempty space, the family `{∅, Ω}` is a sigma-algebra. -/
theorem trivialTwoSetFamily_isSetSigmaAlgebra (Ω : Type u) [Nonempty Ω] :
    IsSetSigmaAlgebra (trivialTwoSetFamily Ω) := by
  exact trivialTwoSetFamily_exists_measurableSpace Ω

-- Proof sketch: realize the full powerset as the measurable sets of the maximal measurable space.
/-- Helper for item (i): realize the full powerset as the measurable sets of a measurable space. -/
theorem powerset_exists_measurableSpace (Ω : Type u) :
    ∃ m : MeasurableSpace Ω, {s : Set Ω | MeasurableSet[m] s} = (univ : Set (Set Ω)) := by
  -- The top measurable space makes every subset measurable.
  refine ⟨⊤, ?_⟩
  ext s
  simp

-- Proof sketch: the full powerset is closed under complements and finite unions.
/-- Part of Example 1.11 (4): On a nonempty space, the full powerset is an algebra of sets. -/
theorem powerset_isSetAlgebra (Ω : Type u) [Nonempty Ω] :
    IsSetAlgebra (univ : Set (Set Ω)) := by
  refine
    { empty_mem := by simp
      compl_mem := by
        intro s hs
        simp
      union_mem := by
        intro s t hs ht
        simp }

-- Proof sketch: realize the full powerset as the underlying family of a Dynkin system.
/-- Part of Example 1.11 (5): On a nonempty space, the full powerset is a lambda-system. -/
theorem powerset_isSetLambdaSystem (Ω : Type u) [Nonempty Ω] :
    IsSetLambdaSystem (univ : Set (Set Ω)) := by
  refine ⟨DynkinSystem.generate (univ : Set (Set Ω)), ?_⟩
  simpa using generatedDynkin_eq_of_existsMeasurableSpace (powerset_exists_measurableSpace Ω)

-- Proof sketch: reuse the explicit measurable-space realization of the full powerset.
/-- Part of Example 1.11 (6): On a nonempty space, the full powerset is a sigma-algebra. -/
theorem powerset_isSetSigmaAlgebra (Ω : Type u) [Nonempty Ω] :
    IsSetSigmaAlgebra (univ : Set (Set Ω)) := by
  exact powerset_exists_measurableSpace Ω

-- Proof sketch: check directly that `{∅}` is closed under the sigma-ring operations.
/-- Part of Example 1.11 (7): On a nonempty space, the family `{∅}` is a sigma-ring. -/
theorem emptySetFamily_isSetSigmaRing (Ω : Type u) [Nonempty Ω] :
    IsSetSigmaRing (emptySetFamily Ω) := by
  refine
    { empty_mem := by simp [emptySetFamily]
      union_mem := ?_
      diff_mem := ?_
      iUnion_mem := ?_ }
  · -- The only available members are both equal to `∅`.
    intro s t hs ht
    have hs' : s = ∅ := by
      simpa [emptySetFamily] using hs
    have ht' : t = ∅ := by
      simpa [emptySetFamily] using ht
    simp [emptySetFamily, hs', ht']
  · -- Differences of `∅` from `∅` remain empty.
    intro s t hs ht
    have hs' : s = ∅ := by
      simpa [emptySetFamily] using hs
    have ht' : t = ∅ := by
      simpa [emptySetFamily] using ht
    simp [emptySetFamily, hs', ht']
  · -- A countable union of empty sets is still empty.
    intro s hs
    have hs' : ∀ n, s n = ∅ := by
      intro n
      simpa [emptySetFamily] using hs n
    have hUnion : (⋃ n, s n : Set Ω) = ∅ := by
      ext x
      simp [hs']
    simp [emptySetFamily, hUnion]

/-- Part of Example 1.11 (8): On a nonempty space, the family `{∅}` is a ring of sets. -/
theorem emptySetFamily_isSetRing (Ω : Type u) [Nonempty Ω] :
    IsSetRing (emptySetFamily Ω) :=
  (emptySetFamily_isSetSigmaRing Ω).toIsSetRing

/-- Part of Example 1.11 (9): On a nonempty space, the family `{∅}` is a semiring of sets. -/
theorem emptySetFamily_isSetSemiring (Ω : Type u) [Nonempty Ω] :
    IsSetSemiring (emptySetFamily Ω) :=
  (emptySetFamily_isSetRing Ω).isSetSemiring

-- Proof sketch: use the canonical sigma-ring structure on the full powerset.
/-- Part of Example 1.11 (10): On a nonempty space, the full powerset is a sigma-ring. -/
theorem powerset_isSetSigmaRing (Ω : Type u) [Nonempty Ω] :
    IsSetSigmaRing (univ : Set (Set Ω)) := by
  -- This is the canonical instance provided in `Definition_1_8`.
  infer_instance

/-- Part of Example 1.11 (11): On a nonempty space, the full powerset is a ring of sets. -/
theorem powerset_isSetRing (Ω : Type u) [Nonempty Ω] :
    IsSetRing (univ : Set (Set Ω)) :=
  (powerset_isSetSigmaRing Ω).toIsSetRing

/-- Part of Example 1.11 (12): On a nonempty space, the full powerset is a semiring of sets. -/
theorem powerset_isSetSemiring (Ω : Type u) [Nonempty Ω] :
    IsSetSemiring (univ : Set (Set Ω)) :=
  (powerset_isSetRing Ω).isSetSemiring

-- Proof sketch: countable subsets of `ℝ` are closed under `∅`, difference, and countable union.
/-- Part of Example 1.11 (13): The countable subsets of `ℝ` form a sigma-ring. -/
theorem countableSubsetFamily_isSetSigmaRing :
    IsSetSigmaRing countableSubsetFamily := by
  refine
    { empty_mem := by simp [countableSubsetFamily]
      union_mem := ?_
      diff_mem := ?_
      iUnion_mem := ?_ }
  · -- Finite unions of countable sets are countable.
    intro s t hs ht
    simpa [countableSubsetFamily] using hs.union ht
  · -- A difference is a subset of its left operand.
    intro s t hs ht
    simpa [countableSubsetFamily] using hs.mono diff_subset
  · -- Countable unions of countable sets are countable.
    intro s hs
    simpa [countableSubsetFamily] using Set.countable_iUnion hs

-- Proof sketch: apply mathlib's semiring-of-sets result for half-open intervals `(a, b]`.
/-- Part of Example 1.11 (14): The family of intervals `(a, b]` with `a ≤ b`
is a semiring on `ℝ`. -/
theorem rightClosedIntervalFamily_isSetSemiring :
    IsSetSemiring rightClosedIntervalFamily := by
  -- This is mathlib's canonical semiring-of-sets structure on half-open intervals.
  simpa [rightClosedIntervalFamily] using
    (MeasureTheory.IsSetSemiring.Ioc : IsSetSemiring rightClosedIntervalFamily)

-- Proof sketch: exhibit two right-closed intervals whose union is not another right-closed
-- interval `(a, b]`.
/-- Part of Example 1.11 (15): The family of intervals `(a, b]` is not a ring of sets. -/
theorem rightClosedIntervalFamily_not_isSetRing :
    ¬ IsSetRing rightClosedIntervalFamily := by
  intro hRing
  have h01 : Ioc (0 : ℝ) 1 ∈ rightClosedIntervalFamily := by
    refine ⟨0, 1, ?_, rfl⟩
    norm_num
  have h23 : Ioc (2 : ℝ) 3 ∈ rightClosedIntervalFamily := by
    exact ⟨2, 3, by norm_num, rfl⟩
  have hUnion : Ioc (0 : ℝ) 1 ∪ Ioc (2 : ℝ) 3 ∈ rightClosedIntervalFamily :=
    hRing.union_mem h01 h23
  rcases (by simpa [rightClosedIntervalFamily] using hUnion) with ⟨a, b, hab, hEq⟩
  -- The interval representation would force every point between `1` and `2` to belong as well.
  have h1 : (1 : ℝ) ∈ Ioc a b := by
    have hLeft : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 := by
      constructor <;> norm_num
    have : (1 : ℝ) ∈ Ioc (0 : ℝ) 1 ∪ Ioc (2 : ℝ) 3 := Or.inl hLeft
    rw [← hEq]
    exact this
  have h3 : (3 : ℝ) ∈ Ioc a b := by
    have hRight : (3 : ℝ) ∈ Ioc (2 : ℝ) 3 := by
      constructor <;> norm_num
    have : (3 : ℝ) ∈ Ioc (0 : ℝ) 1 ∪ Ioc (2 : ℝ) 3 := Or.inr hRight
    rw [← hEq]
    exact this
  have hMid : (2 : ℝ) ∈ Ioc a b := by
    rcases h1 with ⟨ha1, h1b⟩
    rcases h3 with ⟨ha3, h3b⟩
    constructor
    · linarith
    · linarith
  have hNotMid : (2 : ℝ) ∉ Ioc (0 : ℝ) 1 ∪ Ioc (2 : ℝ) 3 := by
    norm_num
  exact hNotMid <| by simpa [hEq] using hMid

-- Proof sketch: finite unions of bounded intervals are closed under `∅`, binary unions, and set
-- differences by refining interval decompositions.
/-- Helper: the ord-connected subsets of `ℝ` form a semiring of sets. -/
lemma ordConnectedFamily_isSetSemiring :
    IsSetSemiring {s : Set ℝ | s.OrdConnected} := by
  refine
    { empty_mem := ordConnected_empty
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · -- Intersections of ord-connected sets remain ord-connected.
    intro s hs t ht
    exact hs.inter ht
  · intro s hs t ht
    classical
    by_cases htEmpty : t = ∅
    · -- If the right operand is empty, the difference is just the left generator.
      refine ⟨{s}, ?_, ?_, ?_⟩
      · intro u hu
        have hu' : u = s := by simpa using hu
        simpa [hu'] using hs
      · intro u hu v hv hne
        have hu' : u = s := by simpa using hu
        have hv' : v = s := by simpa using hv
        exact False.elim (hne (hu'.trans hv'.symm))
      · simp [htEmpty]
    · -- Route correction: decompose `s \ t` using the two closure cuts of `t`.
      let upperCut : Set ℝ := s ∩ ((↑(upperClosure t) : Set ℝ)ᶜ)
      let lowerCut : Set ℝ := s ∩ ((↑(lowerClosure t) : Set ℝ)ᶜ)
      have hUpperCut : upperCut.OrdConnected := by
        -- The upper-cut is the intersection of `s` with a lower set.
        have hLower : IsLowerSet ((↑(upperClosure t) : Set ℝ)ᶜ) := by
          exact isLowerSet_compl.mpr (UpperSet.upper _)
        exact hs.inter hLower.ordConnected
      have hLowerCut : lowerCut.OrdConnected := by
        -- The lower-cut is the intersection of `s` with an upper set.
        have hUpper : IsUpperSet ((↑(lowerClosure t) : Set ℝ)ᶜ) := by
          exact isUpperSet_compl.mpr (LowerSet.lower _)
        exact hs.inter hUpper.ordConnected
      have hDisjCuts :
          Disjoint ((↑(upperClosure t) : Set ℝ)ᶜ) ((↑(lowerClosure t) : Set ℝ)ᶜ) := by
        -- A nonempty ord-connected set cannot lie simultaneously strictly above and strictly below
        -- the same point.
        rw [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
        intro x hx
        rw [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_compl_iff] at hx
        rcases Set.nonempty_iff_ne_empty.mpr htEmpty with ⟨y, hy⟩
        have hxy : x ≤ y := by
          exact le_of_lt (lt_of_not_ge fun hyx ↦ hx.1 ⟨y, hy, hyx⟩)
        exact hx.2 ⟨y, hy, hxy⟩
      have hUpperCutSubset : upperCut ⊆ s \ t := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        exact fun hxt ↦ hx.2 (subset_upperClosure hxt)
      have hLowerCutSubset : lowerCut ⊆ s \ t := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        exact fun hxt ↦ hx.2 (subset_lowerClosure hxt)
      have hDiffToCuts : ∀ ⦃x : ℝ⦄, x ∈ s \ t → x ∈ upperCut ∨ x ∈ lowerCut := by
        intro x hx
        by_cases hxUpper : x ∈ (↑(upperClosure t) : Set ℝ)
        · right
          refine ⟨hx.1, ?_⟩
          rw [Set.mem_compl_iff]
          intro hxLower
          have hx_mem_t : x ∈ t := by
            simpa [Set.mem_inter_iff, ht.upperClosure_inter_lowerClosure] using
              show x ∈ (↑(upperClosure t) : Set ℝ) ∩ ↑(lowerClosure t) from ⟨hxUpper, hxLower⟩
          exact hx.2 hx_mem_t
        · left
          exact ⟨hx.1, by simpa [Set.mem_compl_iff] using hxUpper⟩
      by_cases hCuts : upperCut = lowerCut
      · refine ⟨{upperCut}, ?_, ?_, ?_⟩
        · -- If the two cuts coincide, a singleton witness suffices.
          intro u hu
          have huEq : u = upperCut := by simpa using hu
          simpa [huEq] using hUpperCut
        · intro u hu v hv hne
          have huEq : u = upperCut := by simpa using hu
          have hvEq : v = upperCut := by simpa using hv
          exact False.elim (hne (huEq.trans hvEq.symm))
        · ext x
          constructor
          · intro hx
            rcases hDiffToCuts hx with hxCut | hxCut
            · exact Set.mem_sUnion.mpr ⟨upperCut, by simp, hxCut⟩
            · exact Set.mem_sUnion.mpr ⟨upperCut, by simp, hCuts ▸ hxCut⟩
          · intro hx
            rcases Set.mem_sUnion.mp hx with ⟨u, hu, hxu⟩
            have huEq : u = upperCut := by simpa using hu
            exact hUpperCutSubset (huEq ▸ hxu)
      · refine ⟨{upperCut, lowerCut}, ?_, ?_, ?_⟩
        · -- With distinct cuts, both members lie in the generator family.
          intro u hu
          have huEq : u = upperCut ∨ u = lowerCut := by
            simpa [hCuts] using hu
          rcases huEq with rfl | rfl
          · exact hUpperCut
          · exact hLowerCut
        · -- The distinct closure cuts are disjoint.
          intro u hu v hv hne
          have huEq : u = upperCut ∨ u = lowerCut := by
            simpa [hCuts] using hu
          have hvEq : v = upperCut ∨ v = lowerCut := by
            simpa [hCuts] using hv
          rcases huEq with rfl | rfl <;> rcases hvEq with rfl | rfl
          · exact False.elim (hne rfl)
          · exact Disjoint.mono inter_subset_right inter_subset_right hDisjCuts
          · exact Disjoint.symm <| Disjoint.mono inter_subset_right inter_subset_right hDisjCuts
          · exact False.elim (hne rfl)
        · -- The two closure cuts cover the whole difference.
          ext x
          constructor
          · intro hx
            rcases hDiffToCuts hx with hxCut | hxCut
            · exact Set.mem_sUnion.mpr ⟨upperCut, by simp [hCuts], hxCut⟩
            · exact Set.mem_sUnion.mpr ⟨lowerCut, by simp, hxCut⟩
          · intro hx
            rcases Set.mem_sUnion.mp hx with ⟨u, hu, hxu⟩
            have huEq : u = upperCut ∨ u = lowerCut := by
              simpa [hCuts] using hu
            rcases huEq with rfl | rfl
            · exact hUpperCutSubset hxu
            · exact hLowerCutSubset hxu

/-- Helper: bounded ord-connected subsets of `ℝ` form a semiring of sets. -/
lemma boundedOrdConnectedFamily_isSetSemiring :
    IsSetSemiring {s : Set ℝ | s.OrdConnected ∧ BddBelow s ∧ BddAbove s} := by
  refine
    { empty_mem := by
        simp [ordConnected_empty]
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · -- Intersections preserve ord-connectedness and inherit both bounds.
    intro s hs t ht
    refine ⟨hs.1.inter ht.1, hs.2.1.mono inter_subset_left, hs.2.2.mono inter_subset_left⟩
  · intro s hs t ht
    classical
    obtain ⟨I, hI, hPairwise, hEq⟩ :=
      ordConnectedFamily_isSetSemiring.diff_eq_sUnion' s hs.1 t ht.1
    refine ⟨I, ?_, hPairwise, hEq⟩
    intro u hu
    have huSubset : u ⊆ s := by
      intro x hx
      have hxUnion : x ∈ ⋃₀ (↑I : Set (Set ℝ)) := Set.mem_sUnion.mpr ⟨u, by simpa using hu, hx⟩
      have hxDiff : x ∈ s \ t := by simpa [hEq] using hxUnion
      exact hxDiff.1
    exact ⟨hI hu, hs.2.1.mono huSubset, hs.2.2.mono huSubset⟩

/-- Helper: `finiteUnionIntervalFamily` is the `supClosure` of ord-connected
subsets of `ℝ`. -/
lemma finiteUnionIntervalFamily_eq_supClosure_ordConnected :
    finiteUnionIntervalFamily = supClosure {s : Set ℝ | s.OrdConnected} := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨S, hS, hEq⟩
    by_cases hne : S.Nonempty
    · -- A nonempty finite union is already one of the finite suprema in `supClosure`.
      have hSup : S.sup' hne id = s := by
        calc
          S.sup' hne id = S.sup id := Finset.sup'_eq_sup hne id
          _ = ⋃₀ (↑S : Set (Set ℝ)) := Finset.sup_id_set_eq_sUnion S
          _ = s := hEq.symm
      exact ⟨S, hne, hS, hSup⟩
    · -- The empty finite union is `∅`, which we repackage as the singleton family `{∅}`.
      have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hsEmpty : s = ∅ := by simpa [hS0] using hEq
      refine ⟨{∅}, by simp, ?_, ?_⟩
      · intro t ht
        have ht0 : t = ∅ := by simpa using ht
        simpa [ht0] using (ordConnected_empty : (∅ : Set ℝ).OrdConnected)
      · simp [hsEmpty]
  · intro hs
    rcases hs with ⟨S, hne, hS, hEq⟩
    -- Every finite sup in the closure is literally a finite union of generators.
    have hUnion : ⋃₀ (↑S : Set (Set ℝ)) = s := by
      calc
        ⋃₀ (↑S : Set (Set ℝ)) = S.sup id := (Finset.sup_id_set_eq_sUnion S).symm
        _ = S.sup' hne id := (Finset.sup'_eq_sup hne id).symm
        _ = s := hEq
    exact ⟨S, hS, hUnion.symm⟩

/-- Helper: `finiteUnionBoundedIntervalFamily` is the `supClosure` of bounded
ord-connected subsets of `ℝ`. -/
lemma finiteUnionBoundedIntervalFamily_eq_supClosure_boundedOrdConnected :
    finiteUnionBoundedIntervalFamily =
      supClosure {s : Set ℝ | s.OrdConnected ∧ BddBelow s ∧ BddAbove s} := by
  ext s
  constructor
  · intro hs
    rcases hs with ⟨S, hS, hEq⟩
    by_cases hne : S.Nonempty
    · -- A nonempty bounded finite union is already one of the finite suprema in `supClosure`.
      have hSup : S.sup' hne id = s := by
        calc
          S.sup' hne id = S.sup id := Finset.sup'_eq_sup hne id
          _ = ⋃₀ (↑S : Set (Set ℝ)) := Finset.sup_id_set_eq_sUnion S
          _ = s := hEq.symm
      exact ⟨S, hne, hS, hSup⟩
    · -- The empty finite union is again reindexed by the singleton family `{∅}`.
      have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hsEmpty : s = ∅ := by simpa [hS0] using hEq
      refine ⟨{∅}, by simp, ?_, ?_⟩
      · intro t ht
        have ht0 : t = ∅ := by simpa using ht
        simp [ht0, ordConnected_empty]
      · simp [hsEmpty]
  · intro hs
    rcases hs with ⟨S, hne, hS, hEq⟩
    -- Every finite sup in the closure is literally a finite union of bounded generators.
    have hUnion : ⋃₀ (↑S : Set (Set ℝ)) = s := by
      calc
        ⋃₀ (↑S : Set (Set ℝ)) = S.sup id := (Finset.sup_id_set_eq_sUnion S).symm
        _ = S.sup' hne id := (Finset.sup'_eq_sup hne id).symm
        _ = s := hEq
    exact ⟨S, hS, hUnion.symm⟩

/-- Part of Example 1.11 (16): The finite unions of bounded intervals form a ring on `ℝ`. -/
theorem finiteUnionBoundedIntervalFamily_isSetRing :
    IsSetRing finiteUnionBoundedIntervalFamily := by
  -- Route correction: pass to the generator semiring of bounded ord-connected sets and use the
  -- canonical ring structure on its `supClosure`.
  simpa [finiteUnionBoundedIntervalFamily_eq_supClosure_boundedOrdConnected] using
    boundedOrdConnectedFamily_isSetSemiring.isSetRing_supClosure

-- Proof sketch: the complement of a bounded interval union can contain an
-- unbounded interval and so leave the family.
/-- Part of Example 1.11 (17): The finite unions of bounded intervals do not
form an algebra of sets. -/
theorem finiteUnionBoundedIntervalFamily_not_isSetAlgebra :
    ¬ IsSetAlgebra finiteUnionBoundedIntervalFamily := by
  intro hA
  have hIcc : Icc (0 : ℝ) 1 ∈ finiteUnionBoundedIntervalFamily := by
    -- A single bounded interval is one of the allowed generators.
    refine ⟨{Icc (0 : ℝ) 1}, ?_, ?_⟩
    · intro t ht
      have htIcc : t = Icc (0 : ℝ) 1 := by simpa using ht
      rcases htIcc with rfl
      exact
        ⟨ordConnected_Icc,
          ⟨⟨0, fun x hx ↦ hx.1⟩,
            ⟨1, fun x hx ↦ hx.2⟩⟩⟩
    · simp
  have hComplMem : (Icc (0 : ℝ) 1 : Set ℝ)ᶜ ∈ finiteUnionBoundedIntervalFamily := hA.compl_mem hIcc
  have hNotBddAbove : ¬ BddAbove ((Icc (0 : ℝ) 1 : Set ℝ)ᶜ) := by
    intro hBdd
    rcases hBdd with ⟨M, hM⟩
    let x : ℝ := max (M + 1) 2
    have hBig : x ∈ (Icc (0 : ℝ) 1 : Set ℝ)ᶜ := by
      rw [Set.mem_compl_iff, Set.mem_Icc]
      intro hx
      have hTwo : (2 : ℝ) ≤ x := le_max_right _ _
      linarith [hx.2, hTwo]
    have hLe : x ≤ M := hM hBig
    have hLt : M < x := by
      have hStep : M < M + 1 := by linarith
      exact lt_of_lt_of_le hStep (le_max_left _ _)
    exact not_lt_of_ge hLe hLt
  -- Every member of the bounded family is bounded above, so the complement of `Icc 0 1` cannot lie
  -- in the family.
  rcases hComplMem with ⟨S, hS, hEq⟩
  have hBddAbove : BddAbove (⋃₀ (↑S : Set (Set ℝ))) := by
    have hAll : ∀ t ∈ (↑S : Set (Set ℝ)), BddAbove t := by
      intro t ht
      exact (hS t (by simpa using ht)).2.2
    simpa [Set.sUnion_eq_biUnion] using
      (Set.Finite.bddAbove_biUnion S.finite_toSet).2 hAll
  exact hNotBddAbove <| hEq ▸ hBddAbove

-- Proof sketch: finite unions of order-connected sets are closed under complement in `ℝ` and under
-- finite unions.
/-- Helper: finite unions of ord-connected subsets of `ℝ` form a ring of sets. -/
lemma finiteUnionIntervalFamily_isSetRing :
    IsSetRing finiteUnionIntervalFamily := by
  -- The unbounded interval family is the ring generated by the ord-connected semiring.
  simpa [finiteUnionIntervalFamily_eq_supClosure_ordConnected] using
    ordConnectedFamily_isSetSemiring.isSetRing_supClosure

/-- Part of Example 1.11 (18): The finite unions of arbitrary intervals form an algebra on `ℝ`. -/
theorem finiteUnionIntervalFamily_isSetAlgebra :
    IsSetAlgebra finiteUnionIntervalFamily := by
  -- Route correction: recover complements from the ring structure by subtracting from `univ`.
  have hRing : IsSetRing finiteUnionIntervalFamily := finiteUnionIntervalFamily_isSetRing
  have hUniv : (univ : Set ℝ) ∈ finiteUnionIntervalFamily := by
    refine ⟨{univ}, ?_, by simp⟩
    intro t ht
    have htUniv : t = univ := by simpa using ht
    simpa [htUniv] using (ordConnected_univ : (univ : Set ℝ).OrdConnected)
  refine
    { empty_mem := hRing.empty_mem
      compl_mem := ?_
      union_mem := hRing.union_mem }
  · -- Complements are differences from the ambient interval `univ`.
    intro s hs
    simpa [Set.compl_eq_univ_diff] using hRing.diff_mem hUniv hs

/-- Helper: an ord-connected subset of `ℝ` contained in the natural-number image
is finite. -/
lemma ordConnected_subset_natCastRange_finite {s : Set ℝ} (hs : s.OrdConnected)
    (hsubset : s ⊆ Set.range fun n : ℕ ↦ (n : ℝ)) : s.Finite := by
  have hSubsingleton : s.Subsingleton := by
    intro x hx y hy
    rcases hsubset hx with ⟨m, rfl⟩
    rcases hsubset hy with ⟨n, rfl⟩
    by_contra hmn
    rcases lt_or_gt_of_ne hmn with hmn' | hnm'
    · -- A midpoint between two distinct natural points would lie in `s`, contradicting the
      -- discreteness of the natural-number image.
      have hmnNat : m < n := Nat.cast_lt.mp hmn'
      let z : ℝ := m + 1 / 2
      have hz_mem : z ∈ s := by
        refine hs.out hx hy ⟨?_, ?_⟩
        · norm_num [z]
        · have hsucc : ((m + 1 : ℕ) : ℝ) ≤ n := by
            exact_mod_cast Nat.succ_le_of_lt hmnNat
          have hz_lt : z < (n : ℝ) := by
            have hz_lt_succ : z < ((m + 1 : ℕ) : ℝ) := by
              dsimp [z]
              norm_num
            exact lt_of_lt_of_le hz_lt_succ hsucc
          exact le_of_lt hz_lt
      rcases hsubset hz_mem with ⟨k, hk⟩
      have hkLower : m < k := by
        have hmz : (m : ℝ) < z := by
          dsimp [z]
          norm_num
        have : (m : ℝ) < (k : ℝ) := by
          simpa [hk] using hmz
        exact_mod_cast this
      have hkUpper : k < m + 1 := by
        have : (k : ℝ) < ((m + 1 : ℕ) : ℝ) := by
          simpa [hk, z] using (show z < ((m + 1 : ℕ) : ℝ) by norm_num [z])
        exact_mod_cast this
      omega
    · -- The same midpoint contradiction works with the endpoints reversed.
      have hnmNat : n < m := Nat.cast_lt.mp hnm'
      let z : ℝ := n + 1 / 2
      have hz_mem : z ∈ s := by
        refine hs.out hy hx ⟨?_, ?_⟩
        · norm_num [z]
        · have hsucc : ((n + 1 : ℕ) : ℝ) ≤ m := by
            exact_mod_cast Nat.succ_le_of_lt hnmNat
          have hz_lt : z < (m : ℝ) := by
            have hz_lt_succ : z < ((n + 1 : ℕ) : ℝ) := by
              dsimp [z]
              norm_num
            exact lt_of_lt_of_le hz_lt_succ hsucc
          exact le_of_lt hz_lt
      rcases hsubset hz_mem with ⟨k, hk⟩
      have hkLower : n < k := by
        have hnz : (n : ℝ) < z := by
          dsimp [z]
          norm_num
        have : (n : ℝ) < (k : ℝ) := by
          simpa [hk] using hnz
        exact_mod_cast this
      have hkUpper : k < n + 1 := by
        have : (k : ℝ) < ((n + 1 : ℕ) : ℝ) := by
          simpa [hk, z] using (show z < ((n + 1 : ℕ) : ℝ) by norm_num [z])
        exact_mod_cast this
      omega
  exact hSubsingleton.finite

-- Proof sketch: the sigma-algebra generated by finite interval unions contains additional sets,
-- for instance suitable countable unions of separated intervals.
/-- Companion witness for item (v): the sigma-algebra generated by `finiteUnionIntervalFamily`
strictly contains the family itself. -/
theorem finiteUnionIntervalFamily_generatedSigma_ne_self :
    {s : Set ℝ | MeasurableSet[generateFrom finiteUnionIntervalFamily] s} ≠
      finiteUnionIntervalFamily := by
  let natCastRange : Set ℝ := Set.range fun n : ℕ ↦ (n : ℝ)
  have hSingletonMem : ∀ n : ℕ, ({(n : ℝ)} : Set ℝ) ∈ finiteUnionIntervalFamily := by
    intro n
    -- A singleton is a one-piece finite union of ord-connected generators.
    refine ⟨{{(n : ℝ)}}, ?_, by simp⟩
    intro t ht
    have htSingleton : t = ({(n : ℝ)} : Set ℝ) := by simpa using ht
    simpa [htSingleton] using (ordConnected_singleton : ({(n : ℝ)} : Set ℝ).OrdConnected)
  have hNatRangeMeas :
      MeasurableSet[generateFrom finiteUnionIntervalFamily] natCastRange := by
    -- The natural-number image is a countable union of singleton generators.
    have hEq : natCastRange = ⋃ n : ℕ, ({(n : ℝ)} : Set ℝ) := by
      ext x
      simp [natCastRange]
    rw [hEq]
    exact MeasurableSet.iUnion fun n ↦ MeasurableSpace.measurableSet_generateFrom (hSingletonMem n)
  have hNatRangeNotMem : natCastRange ∉ finiteUnionIntervalFamily := by
    intro hMem
    rcases hMem with ⟨S, hS, hEq⟩
    have hFinitePiece : ∀ t ∈ S, t.Finite := by
      intro t ht
      have htSubset : t ⊆ natCastRange := by
        intro x hx
        have hxUnion : x ∈ ⋃₀ (↑S : Set (Set ℝ)) := Set.mem_sUnion.mpr ⟨t, by simpa using ht, hx⟩
        simpa [natCastRange, hEq] using hxUnion
      exact ordConnected_subset_natCastRange_finite (hS t ht) htSubset
    have hFiniteUnion : (⋃₀ (↑S : Set (Set ℝ))).Finite :=
      S.finite_toSet.sUnion (by
        intro t ht
        exact hFinitePiece t (by simpa using ht))
    have hNatRangeFinite : natCastRange.Finite := by
      simpa [hEq] using hFiniteUnion
    have hNatRangeInfinite : natCastRange.Infinite := by
      simpa [natCastRange] using
        (Set.infinite_range_of_injective (fun {m n} h ↦ by exact_mod_cast h) :
          (Set.range fun n : ℕ ↦ (n : ℝ)).Infinite)
    exact hNatRangeInfinite.not_finite hNatRangeFinite
  intro hEq
  have hNatRangeMem : natCastRange ∈ finiteUnionIntervalFamily := by
    rw [← hEq]
    exact hNatRangeMeas
  exact hNatRangeNotMem hNatRangeMem

/-- Part of Example 1.11 (19): The finite unions of arbitrary intervals do not
form a sigma-algebra. -/
theorem finiteUnionIntervalFamily_not_isSetSigmaAlgebra :
    ¬ IsSetSigmaAlgebra finiteUnionIntervalFamily := by
  -- If the family were already a sigma-algebra, generation would not enlarge it.
  intro hSigma
  exact finiteUnionIntervalFamily_generatedSigma_ne_self
    (generatedSigma_eq_of_existsMeasurableSpace hSigma)

/-- Helper for Example 1.11: encode a finite prefix `x : Fin n → E` as a word on
`Finset.range n`. -/
private def initialWord {E : Type u} {n : ℕ} (x : Fin n → E) : ∀ _ : Finset.range n, E :=
  fun i ↦ x ⟨i, Finset.mem_range.mp i.2⟩

/-- Helper for Example 1.11: read a word on `Finset.range n` back as a prefix
indexed by `Fin n`. -/
private def prefixWord {E : Type u} {n : ℕ} (z : ∀ _ : Finset.range n, E) : Fin n → E :=
  fun i ↦ z ⟨i, Finset.mem_range.mpr i.2⟩

/-- Helper for Example 1.11: encoding the decoded word returns the original
word on `Finset.range n`. -/
private theorem initialWord_prefixWord {E : Type u} {n : ℕ} (z : ∀ _ : Finset.range n, E) :
    initialWord (prefixWord z) = z := by
  -- Both descriptions evaluate to the same coordinate on `Finset.range n`.
  ext i
  simp [initialWord, prefixWord]

/-- Helper for Example 1.11: a textbook prefix cylinder is exactly the singleton
cylinder over `Finset.range n`. -/
private theorem setOf_eq_cylinder_singleton {E : Type u} {n : ℕ} (x : Fin n → E) :
    {ω : ℕ → E | ∀ i : Fin n, ω i = x i} =
      cylinder (Finset.range n) ({initialWord x} : Set (∀ _ : Finset.range n, E)) := by
  -- Rewrite membership in the cylinder as agreement of the restricted word.
  ext ω
  rw [mem_cylinder, Set.mem_singleton_iff]
  constructor
  · intro h
    ext i
    exact h ⟨i, Finset.mem_range.mp i.2⟩
  · intro h i
    exact congr_fun h ⟨i, Finset.mem_range.mpr i.2⟩

/-- Helper for Example 1.11: every singleton cylinder on the first `k > 0`
coordinates belongs to `sequenceCylinderFamily E`. -/
private theorem cylinder_singleton_mem_sequenceCylinderFamily {E : Type u} {k : ℕ}
    (hk : 0 < k) (z : ∀ _ : Finset.range k, E) :
    cylinder (Finset.range k) ({z} : Set (∀ _ : Finset.range k, E)) ∈ sequenceCylinderFamily E := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  -- Decode the word to the textbook `Fin (n + 1)`-indexed prefix.
  right
  refine ⟨n, prefixWord z, ?_⟩
  simpa [initialWord_prefixWord] using
    (setOf_eq_cylinder_singleton (x := prefixWord z)).symm

/-- Helper for Example 1.11: a cylinder with finite base set is the union of the
corresponding singleton cylinders. -/
private theorem cylinder_finset_eq_sUnion_singletons {ι : Type*} {α : ι → Type*}
    (s : Finset ι) (S : Finset (∀ i : s, α i)) :
    cylinder s (↑S : Set (∀ i : s, α i)) =
      ⋃₀ ((S.image fun z ↦ cylinder s ({z} : Set (∀ i : s, α i))) : Set (Set (∀ i, α i))) := by
  -- A point belongs to the cylinder exactly when its restriction is one of the finitely many words.
  ext ω
  constructor
  · intro hω
    rw [mem_cylinder] at hω
    refine Set.mem_sUnion.mpr ?_
    refine ⟨cylinder s ({s.restrict ω} : Set (∀ i : s, α i)), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨s.restrict ω, hω, rfl⟩
    · rw [mem_cylinder]
      simp
  · intro hω
    rcases Set.mem_sUnion.mp hω with ⟨u, hu, hωu⟩
    rcases Finset.mem_image.mp hu with ⟨z, hzS, rfl⟩
    rw [mem_cylinder] at hωu ⊢
    have hEq : s.restrict ω = z := by
      simpa using hωu
    simpa [hEq] using hzS

/-- Helper for Example 1.11: singleton cylinders with the same prefix length are
pairwise disjoint. -/
private theorem pairwiseDisjoint_cylinder_singleton_image {ι : Type*} {α : ι → Type*}
    (s : Finset ι) (S : Finset (∀ i : s, α i)) :
    PairwiseDisjoint
      ((S.image fun z ↦ cylinder s ({z} : Set (∀ i : s, α i))) : Set (Set (∀ i, α i))) id := by
  -- Two different singleton cylinders cannot contain the same ambient point.
  rw [Set.PairwiseDisjoint]
  intro a ha b hb hab
  rcases Finset.mem_image.mp ha with ⟨za, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨zb, _, rfl⟩
  refine Set.disjoint_left.mpr ?_
  intro ω hωa hωb
  have hza : s.restrict ω = za := by
    simpa [mem_cylinder] using hωa
  have hzb : s.restrict ω = zb := by
    simpa [mem_cylinder] using hωb
  have hz : za = zb := hza.symm.trans hzb
  exact hab (by simp [hz])

-- Proof sketch: intersections of cylinders are cylinders, and differences split into finitely many
-- disjoint finer cylinders.
/-- Example 1.11 (20): For a finite nonempty set `E`, the family
`A = ⋃ n, sequenceCylinderLevel E n` of cylinders on `E^ℕ` is a semiring of
sets. -/
theorem sequenceCylinderFamily_isSetSemiring {E : Type u} [Finite E] [Nonempty E] :
    IsSetSemiring (sequenceCylinderFamily E) := by
  classical
  refine
    { empty_mem := Or.inl rfl
      inter_mem := ?_
      diff_eq_sUnion' := ?_ }
  · intro s hs t ht
    rcases hs with rfl | ⟨n, x, rfl⟩
    · -- Intersecting with `∅` keeps the empty generator.
      left
      ext ω
      simp
    rcases ht with rfl | ⟨m, y, rfl⟩
    · -- The symmetric empty case is equally immediate.
      left
      ext ω
      simp
    by_cases hnm : n ≤ m
    · -- Compare the two cylinders on the longer prefix length `m + 1`.
      by_cases hcompat : ∀ i : Fin (n + 1),
          x i = y ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩
      · right
        refine ⟨m, y, ?_⟩
        -- A compatible longer prefix determines the whole intersection.
        ext ω
        constructor
        · intro hω
          exact hω.2
        · intro hω
          refine ⟨?_, hω⟩
          intro i
          have hy :
              ω i = y ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩ := by
            simpa using hω ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩
          exact hy.trans (hcompat i).symm
      · left
        push Not at hcompat
        rcases hcompat with ⟨i, hi⟩
        -- An incompatible coordinate makes the intersection empty.
        ext ω
        constructor
        · intro hω
          have hx : ω i = x i := hω.1 i
          have hy : ω i = y ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩ := by
            simpa using hω.2 ⟨i, lt_of_lt_of_le i.2 (Nat.succ_le_succ hnm)⟩
          exact (hi (hx.symm.trans hy)).elim
        · intro hω
          simp at hω
    · have hmn : m ≤ n := Nat.le_of_not_ge hnm
      by_cases hcompat : ∀ j : Fin (m + 1),
          y j = x ⟨j, lt_of_lt_of_le j.2 (Nat.succ_le_succ hmn)⟩
      · right
        refine ⟨n, x, ?_⟩
        -- In the symmetric compatible case, the longer `x`-cylinder survives.
        ext ω
        constructor
        · intro hω
          exact hω.1
        · intro hω
          refine ⟨hω, ?_⟩
          intro j
          have hx :
              ω j = x ⟨j, lt_of_lt_of_le j.2 (Nat.succ_le_succ hmn)⟩ := by
            simpa using hω ⟨j, lt_of_lt_of_le j.2 (Nat.succ_le_succ hmn)⟩
          exact hx.trans (hcompat j).symm
      · left
        push Not at hcompat
        rcases hcompat with ⟨j, hj⟩
        -- An incompatible coordinate again forces the intersection to be empty.
        ext ω
        constructor
        · intro hω
          have hy : ω j = y j := hω.2 j
          have hx : ω j = x ⟨j, lt_of_lt_of_le j.2 (Nat.succ_le_succ hmn)⟩ := by
            simpa using hω.1 ⟨j, lt_of_lt_of_le j.2 (Nat.succ_le_succ hmn)⟩
          exact (hj (hy.symm.trans hx)).elim
        · intro hω
          simp at hω
  · intro s hs t ht
    rcases hs with rfl | ⟨n, x, rfl⟩
    · -- The difference of `∅` from anything is still empty.
      refine ⟨∅, by simp, by simp, ?_⟩
      ext ω
      simp
    rcases ht with rfl | ⟨m, y, rfl⟩
    · -- Subtracting `∅` leaves the original cylinder as a one-piece decomposition.
      refine ⟨{{ω | ∀ i : Fin (n + 1), ω i = x i}}, ?_, ?_, ?_⟩
      · intro u hu
        have hu' : u = {ω | ∀ i : Fin (n + 1), ω i = x i} := by
          simpa using hu
        simpa [hu'] using
          (Or.inr ⟨n, x, rfl⟩ :
            {ω | ∀ i : Fin (n + 1), ω i = x i} ∈ sequenceCylinderFamily E)
      · simp
      · ext ω
        simp
    -- Route correction: instead of a first-mismatch recursion, lift both cylinders to the
    -- common prefix length `max (n + 1) (m + 1)` and decompose the finite base-set difference.
    let K := max (n + 1) (m + 1)
    let Word := ∀ i : Finset.range K, E
    let _ : Fintype Word := Fintype.ofFinite Word
    let Sx : Finset Word :=
      Finset.univ.filter fun z ↦
        ∀ i : Fin (n + 1),
          z ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.2 (Nat.le_max_left _ _))⟩ = x i
    let Sy : Finset Word :=
      Finset.univ.filter fun z ↦
        ∀ i : Fin (m + 1),
          z ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le i.2 (Nat.le_max_right _ _))⟩ = y i
    let I : Finset (Set (ℕ → E)) :=
      (((Sx : Finset Word) \ (Sy : Finset Word)) : Finset Word).image fun z ↦
        cylinder (Finset.range K) ({z} : Set Word)
    have hKpos : 0 < K := by
      dsimp [K]
      exact lt_of_lt_of_le (Nat.succ_pos n) (Nat.le_max_left _ _)
    have hxEq :
        ({ω : ℕ → E | ∀ i : Fin (n + 1), ω i = x i} : Set (ℕ → E)) =
          cylinder (Finset.range K) (↑Sx : Set Word) := by
      -- A word of length `K` belongs to the lifted base exactly when it extends `x`.
      ext ω
      rw [mem_cylinder]
      simp [Sx, Word]
    have hyEq :
        ({ω : ℕ → E | ∀ i : Fin (m + 1), ω i = y i} : Set (ℕ → E)) =
          cylinder (Finset.range K) (↑Sy : Set Word) := by
      -- The second cylinder normalizes in the same way.
      ext ω
      rw [mem_cylinder]
      simp [Sy, Word]
    refine ⟨I, ?_, ?_, ?_⟩
    · -- Each singleton cylinder in the decomposition is one of the textbook generators.
      intro u hu
      rcases Finset.mem_image.mp hu with ⟨z, hz, rfl⟩
      exact cylinder_singleton_mem_sequenceCylinderFamily hKpos z
    · -- The singleton cylinders are pairwise disjoint because they specify different full words.
      simpa [I] using
        pairwiseDisjoint_cylinder_singleton_image (ι := ℕ) (α := fun _ : ℕ ↦ E) (Finset.range K)
          ((((Sx : Finset Word) \ (Sy : Finset Word)) : Finset Word))
    · -- After normalization, the difference is exactly the finite union of singleton cylinders.
      calc
        ({ω : ℕ → E | ∀ i : Fin (n + 1), ω i = x i} : Set (ℕ → E)) \
            {ω : ℕ → E | ∀ i : Fin (m + 1), ω i = y i}
            =
              cylinder (Finset.range K)
                (↑((((Sx : Finset Word) \ (Sy : Finset Word)) : Finset Word)) : Set Word) := by
                rw [hxEq, hyEq, diff_cylinder_same]
                congr 1
                ext z
                simp [Sx, Sy]
        _ = ⋃₀ I := by
              simpa [I] using
                (cylinder_finset_eq_sUnion_singletons (ι := ℕ) (α := fun _ : ℕ ↦ E)
                  (Finset.range K)
                  ((((Sx : Finset Word) \ (Sy : Finset Word)) : Finset Word)))

-- Proof sketch: when `E` has at least two elements, the union of two incompatible cylinders is not
-- again a cylinder or `∅`.
/-- Part of Example 1.11 (21): If `E` is finite and has more than one element, then
the cylinder family on `E^ℕ` is not a ring of sets. -/
theorem sequenceCylinderFamily_not_isSetRing {E : Type u} [Finite E] [Nontrivial E] :
    ¬ IsSetRing (sequenceCylinderFamily E) := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne E
  let firstCylinder : Set (ℕ → E) := {ω | ω 0 = a}
  let secondCylinder : Set (ℕ → E) := {ω | ω 0 = b}
  have hFirst : firstCylinder ∈ sequenceCylinderFamily E := by
    -- A one-step cylinder is one of the basic generators.
    right
    refine ⟨0, (fun _ ↦ a), ?_⟩
    ext ω
    simp [firstCylinder]
  have hSecond : secondCylinder ∈ sequenceCylinderFamily E := by
    -- Likewise for the cylinder fixing the first value to `b`.
    right
    refine ⟨0, (fun _ ↦ b), ?_⟩
    ext ω
    simp [secondCylinder]
  intro hRing
  have hUnion : firstCylinder ∪ secondCylinder ∈ sequenceCylinderFamily E :=
    hRing.union_mem hFirst hSecond
  rcases hUnion with hEmpty | ⟨n, x, hx⟩
  · -- The union contains the constant `a`-sequence, so it cannot be empty.
    have hMem : (fun _ ↦ a) ∈ firstCylinder ∪ secondCylinder := by
      simp [firstCylinder]
    have : (fun _ ↦ a) ∈ (∅ : Set (ℕ → E)) := by
      rw [← hEmpty]
      exact hMem
    simp at this
  · -- Any positive-length cylinder fixes the first coordinate to a single value, but this union
    -- contains both the constant `a`- and the constant `b`-sequence.
    have hMemA : (fun _ ↦ a) ∈ {ω | ∀ i : Fin (n + 1), ω i = x i} := by
      have : (fun _ ↦ a) ∈ firstCylinder ∪ secondCylinder := by
        simp [firstCylinder]
      simpa [hx] using this
    have hMemB : (fun _ ↦ b) ∈ {ω | ∀ i : Fin (n + 1), ω i = x i} := by
      have : (fun _ ↦ b) ∈ firstCylinder ∪ secondCylinder := by
        simp [secondCylinder]
      simpa [hx] using this
    have ha0 : a = x 0 := by
      simpa using hMemA 0
    have hb0 : b = x 0 := by
      simpa using hMemB 0
    exact hab (ha0.trans hb0.symm)

-- Proof sketch: finite and cofinite sets are stable under complements and finite unions.
/-- Part of Example 1.11 (22): On a nonempty space, the finite-or-cofinite
subsets form an algebra of sets. -/
theorem finiteOrCofiniteFamily_isSetAlgebra (Ω : Type u) [Nonempty Ω] :
    IsSetAlgebra (finiteOrCofiniteFamily Ω) := by
  refine
    { empty_mem := by
        simp [finiteOrCofiniteFamily]
      compl_mem := ?_
      union_mem := ?_ }
  · -- Complement swaps the finite and cofinite branches.
    intro s hs
    rcases hs with hs | hs <;> simp [finiteOrCofiniteFamily, hs]
  · -- A union is finite if both parts are finite, and otherwise it is cofinite.
    intro s t hs ht
    rcases hs with hs | hs
    · rcases ht with ht | ht
      · exact Or.inl (hs.union ht)
      · exact Or.inr <| Set.Finite.subset ht <| by
          intro x hx hxt
          exact hx (Or.inr hxt)
    · rcases ht with ht | ht
      · exact Or.inr <| Set.Finite.subset hs <| by
          intro x hx hsx
          exact hx (Or.inl hsx)
      · have hsubset : (s ∪ t)ᶜ ⊆ sᶜ ∪ tᶜ := by
          intro x hx
          exact Or.inl fun hsx ↦ hx (Or.inl hsx)
        exact Or.inr <| Set.Finite.subset (hs.union ht) hsubset

-- Proof sketch: on an infinite space, a countable union of finite sets can be infinite and
-- coinfinite, so the sigma-algebra generated by the family is strictly larger than the family.
/-- Companion spec for the finite-or-cofinite family: on an infinite space,
`generateFrom` adds new sets to the finite-or-cofinite family. -/
theorem finiteOrCofiniteFamily_generatedSigma_ne (Ω : Type u) [Nonempty Ω] [Infinite Ω] :
    {s : Set Ω | MeasurableSet[generateFrom (finiteOrCofiniteFamily Ω)] s} ≠
      finiteOrCofiniteFamily Ω := by
  classical
  let e : ℕ ↪ Ω := Infinite.natEmbedding Ω
  let evenPart : Set Ω := Set.range fun n : ℕ ↦ e (2 * n)
  let oddPart : Set Ω := Set.range fun n : ℕ ↦ e (2 * n + 1)
  have hSingletonMeas :
      ∀ x : Ω, MeasurableSet[generateFrom (finiteOrCofiniteFamily Ω)] ({x} : Set Ω) := by
    intro x
    have hComplGen : ({x} : Set Ω)ᶜ ∈ finiteOrCofiniteFamily Ω := by
      right
      simp
    -- Singletons are complements of generator sets.
    simpa using (MeasurableSpace.measurableSet_generateFrom hComplGen).compl
  have hEvenMeas : MeasurableSet[generateFrom (finiteOrCofiniteFamily Ω)] evenPart := by
    have hEq : evenPart = ⋃ n, ({e (2 * n)} : Set Ω) := by
      ext x
      simp [evenPart]
    rw [hEq]
    exact MeasurableSet.iUnion fun n ↦ hSingletonMeas (e (2 * n))
  have hEvenInfinite : evenPart.Infinite := by
    have hInj : Function.Injective (fun n : ℕ ↦ e (2 * n)) := by
      intro m n h
      apply e.injective at h
      omega
    simpa [evenPart] using Set.infinite_range_of_injective hInj
  have hOddInfinite : oddPart.Infinite := by
    have hInj : Function.Injective (fun n : ℕ ↦ e (2 * n + 1)) := by
      intro m n h
      apply e.injective at h
      omega
    simpa [oddPart] using Set.infinite_range_of_injective hInj
  have hOddSubset : oddPart ⊆ evenPartᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hEven
    rcases hx with ⟨n, rfl⟩
    rcases hEven with ⟨m, hm⟩
    apply e.injective at hm
    omega
  have hEvenNotMem : evenPart ∉ finiteOrCofiniteFamily Ω := by
    intro hEven
    rcases hEven with hEvenFinite | hEvenComplFinite
    · exact hEvenInfinite.not_finite hEvenFinite
    · exact (hOddInfinite.mono hOddSubset).not_finite hEvenComplFinite
  intro hEq
  -- The even image of the natural embedding is generated-measurable but neither
  -- finite nor cofinite.
  have hEvenMem : evenPart ∈ finiteOrCofiniteFamily Ω := by
    rw [← hEq]
    exact hEvenMeas
  exact hEvenNotMem hEvenMem

-- Proof sketch: if the family were already a sigma-algebra, `generateFrom` would add no new sets,
-- contradicting the explicit infinite/coinfinite witness above.
/-- Part of Example 1.11 (23): On an infinite nonempty space, the finite-or-cofinite family is not a
sigma-algebra. -/
theorem finiteOrCofiniteFamily_not_isSetSigmaAlgebra (Ω : Type u) [Nonempty Ω] [Infinite Ω] :
    ¬ IsSetSigmaAlgebra (finiteOrCofiniteFamily Ω) := by
  intro hSigma
  exact finiteOrCofiniteFamily_generatedSigma_ne Ω
    (generatedSigma_eq_of_existsMeasurableSpace hSigma)

-- Proof sketch: realize the countable-or-cocountable family as the measurable sets of a
-- measurable space.
/-- Helper: realize the countable-or-cocountable family as measurable
sets. -/
theorem countableOrCocountableFamily_exists_measurableSpace (Ω : Type u) [Nonempty Ω] :
    ∃ m : MeasurableSpace Ω,
      {s : Set Ω | MeasurableSet[m] s} = countableOrCocountableFamily Ω := by
  -- Bundle the countable-or-cocountable family directly into a measurable space.
  refine ⟨
    { MeasurableSet' := countableOrCocountableFamily Ω
      measurableSet_empty := by
        exact Or.inl Set.countable_empty
      measurableSet_compl := by
        intro s hs
        rcases hs with hs | hs
        · exact Or.inr <| by simpa using hs
        · exact Or.inl hs
      measurableSet_iUnion := by
        intro s hs
        by_cases hcount : ∀ n, (s n).Countable
        · left
          exact Set.countable_iUnion hcount
        · push Not at hcount
          rcases hcount with ⟨n, hn⟩
          have hnCompl : (s n)ᶜ.Countable := by
            rcases hs n with hs_n | hs_n
            · exact False.elim (hn hs_n)
            · exact hs_n
          right
          refine hnCompl.mono ?_
          intro x hx
          have hx' : x ∉ s n := by
            intro hxn
            exact hx <| mem_iUnion.mpr ⟨n, hxn⟩
          simpa [Set.mem_compl_iff] using hx' },
    ?_⟩
  ext s
  rfl

-- Proof sketch: the countable-or-cocountable family is already closed under the sigma-algebra
-- operations, so it directly defines a measurable space.
/-- Part of Example 1.11 (24): On a nonempty space, the countable-or-cocountable subsets form a
sigma-algebra. -/
theorem countableOrCocountableFamily_isSetSigmaAlgebra (Ω : Type u) [Nonempty Ω] :
    IsSetSigmaAlgebra (countableOrCocountableFamily Ω) := by
  exact countableOrCocountableFamily_exists_measurableSpace Ω

/-- Companion spec for the countable-or-cocountable family: `generateFrom` adds no new sets to
the countable-or-cocountable family. -/
theorem countableOrCocountableFamily_generatedSigma_eq (Ω : Type u) [Nonempty Ω] :
    {s : Set Ω | MeasurableSet[generateFrom (countableOrCocountableFamily Ω)] s} =
      countableOrCocountableFamily Ω := by
  -- The explicit measurable-space realization already has exactly this family of measurable sets.
  simpa using generatedSigma_eq_of_existsMeasurableSpace
    (countableOrCocountableFamily_exists_measurableSpace Ω)

-- Proof sketch: the canonical Dynkin system attached to a measurable space has exactly the
-- measurable sets as its underlying family.
/-- Helper for item (ix): the measurable sets of a measurable space form a lambda-system. -/
theorem measurableSet_isSetLambdaSystem {Ω : Type u} (m : MeasurableSpace Ω) :
    IsSetLambdaSystem {s : Set Ω | MeasurableSet[m] s} := by
  exact ⟨DynkinSystem.ofMeasurableSpace m, rfl⟩

/-- Companion spec for item (ix): the canonical Dynkin system attached to a measurable space has
exactly the measurable sets as its underlying family. -/
theorem measurableSet_dynkinHas_eq_measurableSet {Ω : Type u} (m : MeasurableSpace Ω) :
    {s : Set Ω | (DynkinSystem.ofMeasurableSpace m).Has s} =
      {s : Set Ω | MeasurableSet[m] s} := by
  -- This Dynkin-system predicate is definitionally the measurable-set predicate.
  rfl

-- Proof sketch: combine the direct sigma-algebra-to-lambda-system statement with a realization of
-- `A` as the measurable sets of `generateFrom A`.
/-- Part of Example 1.11 (25): Every sigma-algebra is a lambda-system. -/
theorem isSetLambdaSystem_of_isSetSigmaAlgebra {Ω : Type u} {A : Set (Set Ω)}
    (hA : IsSetSigmaAlgebra A) :
    IsSetLambdaSystem A := by
  rcases hA with ⟨m, hm⟩
  refine ⟨DynkinSystem.ofMeasurableSpace m, ?_⟩
  ext s
  rw [← hm]
  rfl

-- Proof sketch: realize the family as the `Has`-predicate of a Dynkin system on `Fin 4`.
/-- Helper for Example 1.11: membership in `fourPointLambdaFamily` means being
one of its six explicit sets. -/
private lemma mem_fourPointLambdaFamily_iff {s : Set (Fin 4)} :
    s ∈ fourPointLambdaFamily ↔
      s = ∅ ∨
        s = ({0, 1} : Set (Fin 4)) ∨
          s = ({0, 3} : Set (Fin 4)) ∨
            s = ({1, 2} : Set (Fin 4)) ∨
              s = ({2, 3} : Set (Fin 4)) ∨
                s = (univ : Set (Fin 4)) := by
  simp [fourPointLambdaFamily]

/-- Helper for Example 1.11: two sets sharing a point are not disjoint. -/
private theorem not_disjoint_of_mem {α : Type*} {s t : Set α} {x : α}
    (hsx : x ∈ s) (htx : x ∈ t) : ¬ Disjoint s t := by
  intro h
  exact h.le_bot ⟨hsx, htx⟩

/-- Helper for Example 1.11: complements preserve the explicit six-set family on
`Fin 4`. -/
private lemma fourPointLambdaFamily_compl_mem {s : Set (Fin 4)}
    (hs : s ∈ fourPointLambdaFamily) : sᶜ ∈ fourPointLambdaFamily := by
  -- Complements just permute the six listed sets.
  rcases mem_fourPointLambdaFamily_iff.mp hs with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [fourPointLambdaFamily]
  · have hcomp : (({0, 1} : Set (Fin 4))ᶜ) = ({2, 3} : Set (Fin 4)) := by
      ext x
      fin_cases x <;> simp
    simp [hcomp, fourPointLambdaFamily]
  · have hcomp : (({0, 3} : Set (Fin 4))ᶜ) = ({1, 2} : Set (Fin 4)) := by
      ext x
      fin_cases x <;> simp
    simp [hcomp, fourPointLambdaFamily]
  · have hcomp : (({1, 2} : Set (Fin 4))ᶜ) = ({0, 3} : Set (Fin 4)) := by
      ext x
      fin_cases x <;> simp
    simp [hcomp, fourPointLambdaFamily]
  · have hcomp : (({2, 3} : Set (Fin 4))ᶜ) = ({0, 1} : Set (Fin 4)) := by
      ext x
      fin_cases x <;> simp
    simp [hcomp, fourPointLambdaFamily]
  · simp [fourPointLambdaFamily]

/-- Helper for Example 1.11: a nonempty proper member of the explicit six-set
family only admits `∅` or its complement as a disjoint partner in the family. -/
private lemma fourPointLambdaFamily_eq_empty_or_compl_of_disjoint {s t : Set (Fin 4)}
    (hs : s ∈ fourPointLambdaFamily) (ht : t ∈ fourPointLambdaFamily) (hs_nonempty : s ≠ ∅)
    (hs_not_univ : s ≠ univ) (hdisj : Disjoint s t) :
    t = ∅ ∨ t = sᶜ := by
  classical
  rcases mem_fourPointLambdaFamily_iff.mp hs with hs' | hs' | hs' | hs' | hs' | hs'
  · exact (hs_nonempty hs').elim
  · subst hs'
    rcases mem_fourPointLambdaFamily_iff.mp ht with ht' | ht' | ht' | ht' | ht' | ht'
    · exact Or.inl ht'
    · subst ht'
      have hnot : ¬ Disjoint ({0, 1} : Set (Fin 4)) ({0, 1} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 0) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({0, 1} : Set (Fin 4)) ({0, 3} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 0) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({0, 1} : Set (Fin 4)) ({1, 2} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 1) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      right
      ext x
      fin_cases x <;> simp
    · subst ht'
      have hnot : ¬ Disjoint ({0, 1} : Set (Fin 4)) (univ : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 0) (by simp) (by simp)
      exact (hnot hdisj).elim
  · subst hs'
    rcases mem_fourPointLambdaFamily_iff.mp ht with ht' | ht' | ht' | ht' | ht' | ht'
    · exact Or.inl ht'
    · subst ht'
      have hnot : ¬ Disjoint ({0, 3} : Set (Fin 4)) ({0, 1} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 0) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({0, 3} : Set (Fin 4)) ({0, 3} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 0) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      right
      ext x
      fin_cases x <;> simp
    · subst ht'
      have hnot : ¬ Disjoint ({0, 3} : Set (Fin 4)) ({2, 3} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 3) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({0, 3} : Set (Fin 4)) (univ : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 0) (by simp) (by simp)
      exact (hnot hdisj).elim
  · subst hs'
    rcases mem_fourPointLambdaFamily_iff.mp ht with ht' | ht' | ht' | ht' | ht' | ht'
    · exact Or.inl ht'
    · subst ht'
      have hnot : ¬ Disjoint ({1, 2} : Set (Fin 4)) ({0, 1} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 1) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      right
      ext x
      fin_cases x <;> simp
    · subst ht'
      have hnot : ¬ Disjoint ({1, 2} : Set (Fin 4)) ({1, 2} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 1) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({1, 2} : Set (Fin 4)) ({2, 3} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 2) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({1, 2} : Set (Fin 4)) (univ : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 1) (by simp) (by simp)
      exact (hnot hdisj).elim
  · subst hs'
    rcases mem_fourPointLambdaFamily_iff.mp ht with ht' | ht' | ht' | ht' | ht' | ht'
    · exact Or.inl ht'
    · subst ht'
      right
      ext x
      fin_cases x <;> simp
    · subst ht'
      have hnot : ¬ Disjoint ({2, 3} : Set (Fin 4)) ({0, 3} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 3) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({2, 3} : Set (Fin 4)) ({1, 2} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 2) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({2, 3} : Set (Fin 4)) ({2, 3} : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 2) (by simp) (by simp)
      exact (hnot hdisj).elim
    · subst ht'
      have hnot : ¬ Disjoint ({2, 3} : Set (Fin 4)) (univ : Set (Fin 4)) :=
        not_disjoint_of_mem (x := 2) (by simp) (by simp)
      exact (hnot hdisj).elim
  · exact (hs_not_univ hs').elim

/-- Helper: disjoint binary unions inside `fourPointLambdaFamily` stay in the
family. -/
lemma fourPointLambdaFamily_disjointUnion_mem {s t : Set (Fin 4)}
    (hs : s ∈ fourPointLambdaFamily) (ht : t ∈ fourPointLambdaFamily) (hdisj : Disjoint s t) :
    s ∪ t ∈ fourPointLambdaFamily := by
  by_cases hsEmpty : s = ∅
  · simpa [hsEmpty] using ht
  by_cases hsUniv : s = univ
  · have htEmpty : t = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hxt
      have hsx : x ∈ s := by simp [hsUniv]
      exact hdisj.le_bot ⟨hsx, hxt⟩
    simp [hsUniv, htEmpty, fourPointLambdaFamily]
  rcases fourPointLambdaFamily_eq_empty_or_compl_of_disjoint hs ht hsEmpty hsUniv hdisj with
    rfl | hCompl
  · simpa using hs
  · have hUnion : s ∪ t = (univ : Set (Fin 4)) := by
      simp [hCompl]
    simp [hUnion, fourPointLambdaFamily]

/-- Helper: finite pairwise disjoint unions of sets in `fourPointLambdaFamily`
remain in the family. -/
lemma fourPointLambdaFamily_biUnion_mem {ι : Type*} (S : Finset ι)
    {f : ι → Set (Fin 4)} (hmem : ∀ i ∈ S, f i ∈ fourPointLambdaFamily)
    (hdisj : (↑S : Set ι).Pairwise (fun i j ↦ Disjoint (f i) (f j))) :
    (⋃ i ∈ S, f i) ∈ fourPointLambdaFamily := by
  classical
  induction S using Finset.induction with
  | empty =>
      -- The empty indexed union is `∅`.
      simp [fourPointLambdaFamily]
  | @insert a S haS ih =>
      have ha : f a ∈ fourPointLambdaFamily := hmem a (by simp)
      have hS :
          (⋃ i ∈ S, f i) ∈ fourPointLambdaFamily := by
        apply ih
        · intro i hi
          exact hmem i (by simp [hi])
        · intro i hi j hj hij
          exact hdisj (by simp [hi]) (by simp [hj]) hij
      have hdisjUnion : Disjoint (f a) (⋃ i ∈ S, f i) := by
        -- The inserted term is disjoint from each remaining piece, hence from their union.
        refine Set.disjoint_left.mpr ?_
        intro x hxa hxUnion
        rcases Set.mem_iUnion.mp hxUnion with ⟨i, hxUnion⟩
        rcases Set.mem_iUnion.mp hxUnion with ⟨hi, hxi⟩
        have hai : a ≠ i := by
          intro hEq
          subst hEq
          exact haS hi
        exact (hdisj (by simp) (by simp [hi]) hai).le_bot ⟨hxa, hxi⟩
      -- Reassociate the finite union as a binary disjoint union.
      simpa [Finset.set_biUnion_insert, haS] using
        fourPointLambdaFamily_disjointUnion_mem ha hS hdisjUnion

/-- Helper: countable pairwise disjoint unions of members of
`fourPointLambdaFamily` remain in the family. -/
lemma fourPointLambdaFamily_iUnion_mem {f : ℕ → Set (Fin 4)}
    (hdisj : Pairwise (fun i j ↦ Disjoint (f i) (f j)))
    (hmem : ∀ n, f n ∈ fourPointLambdaFamily) :
    (⋃ n, f n) ∈ fourPointLambdaFamily := by
  classical
  by_cases hEmpty : ∀ n, f n = ∅
  · -- If every term is empty, then so is the union.
    have hUnion : (⋃ n, f n) = ∅ := by
      ext x
      simp [hEmpty]
    simp [hUnion, fourPointLambdaFamily]
  have hExistsNonempty : ∃ n, f n ≠ ∅ := by
    by_contra hNo
    apply hEmpty
    intro n
    by_contra hn
    exact hNo ⟨n, hn⟩
  obtain ⟨n0, hn0⟩ := hExistsNonempty
  by_cases hUniv : f n0 = univ
  · -- If one piece is already `univ`, then the whole union is `univ`.
    have hUnion : (⋃ n, f n) = univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        have hx0 : x ∈ f n0 := by simp [hUniv]
        exact Set.mem_iUnion.mpr ⟨n0, hx0⟩
    simp [hUnion, fourPointLambdaFamily]
  have hPartners :
      ∀ n, n ≠ n0 → f n = ∅ ∨ f n = (f n0)ᶜ := by
    intro n hn
    have hd : Disjoint (f n0) (f n) := hdisj (by simpa using hn.symm)
    exact fourPointLambdaFamily_eq_empty_or_compl_of_disjoint
      (hmem n0) (hmem n) hn0 hUniv hd
  by_cases hSecond : ∃ n, n ≠ n0 ∧ f n ≠ ∅
  · obtain ⟨n1, hn1, hn1_nonempty⟩ := hSecond
    rcases hPartners n1 hn1 with hEmpty1 | hCompl
    · exact (hn1_nonempty hEmpty1).elim
    -- Once the complement of `f n0` appears, the union is already `univ`.
    have hUnion : (⋃ n, f n) = univ := by
      ext x
      constructor
      · intro _
        simp
      · intro _
        have hxPair : x ∈ f n0 ∪ f n1 := by
          simp [hCompl]
        rcases hxPair with hx0 | hx1
        · exact Set.mem_iUnion.mpr ⟨n0, hx0⟩
        · exact Set.mem_iUnion.mpr ⟨n1, hx1⟩
    simp [hUnion, fourPointLambdaFamily]
  · have hRestEmpty : ∀ n, n ≠ n0 → f n = ∅ := by
      intro n hn
      rcases hPartners n hn with hEq | hEq
      · exact hEq
      · exfalso
        exact hSecond ⟨n, hn, by simpa [hEq]⟩
    -- Otherwise the first nonempty set is the whole countable disjoint union.
    have hUnion : (⋃ n, f n) = f n0 := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨n, hxn⟩
        by_cases hn : n = n0
        · simpa [hn] using hxn
        · have hfn : f n = ∅ := hRestEmpty n hn
          simp [hfn] at hxn
      · intro hx
        exact Set.mem_iUnion.mpr ⟨n0, hx⟩
    simpa [hUnion] using hmem n0

/-- Helper for item (x): realize the explicit six-set family as the underlying family of a
Dynkin system. -/
theorem fourPointLambdaFamily_exists_dynkinSystem :
    ∃ d : DynkinSystem (Fin 4), d.Has = fourPointLambdaFamily := by
  have hEmpty : (∅ : Set (Fin 4)) ∈ fourPointLambdaFamily := by
    simp [fourPointLambdaFamily]
  refine ⟨
    { Has := fourPointLambdaFamily
      has_empty := hEmpty
      has_compl := by
        intro s hs
        -- Complements remain within the six explicit members.
        exact fourPointLambdaFamily_compl_mem hs
      has_iUnion_nat := by
        intro f hdisj hf
        -- Countable disjoint unions reduce to the explicit finite-family argument above.
        exact fourPointLambdaFamily_iUnion_mem hdisj hf },
    rfl⟩

-- Proof sketch: reuse the explicit Dynkin-system realization of the family.
/-- Part of Example 1.11 (26): The explicit six-set family on `Fin 4` is a lambda-system. -/
theorem fourPointLambdaFamily_isLambdaSystem :
    IsSetLambdaSystem fourPointLambdaFamily := by
  exact fourPointLambdaFamily_exists_dynkinSystem

/-- Companion spec for item (x): λ-generation adds no new sets to the explicit six-set family. -/
theorem fourPointLambdaFamily_generatedDynkin_eq :
    {s : Set (Fin 4) | (DynkinSystem.generate fourPointLambdaFamily).Has s} =
      fourPointLambdaFamily := by
  ext s
  constructor
  · intro hs
    rcases fourPointLambdaFamily_exists_dynkinSystem with ⟨d, hd⟩
    have hle : DynkinSystem.generate fourPointLambdaFamily ≤ d := by
      refine DynkinSystem.generate_le (d := d) ?_
      intro t ht
      simpa [hd] using ht
    simpa [hd] using hle s hs
  · intro hs
    exact DynkinSystem.GenerateHas.basic s hs

-- Proof sketch: one checks that this family is not closed under complements, so it cannot be an
-- algebra of sets.
/-- Part of Example 1.11 (27): The explicit six-set family on `Fin 4` is not an algebra of sets. -/
theorem fourPointLambdaFamily_not_isSetAlgebra :
    ¬ IsSetAlgebra fourPointLambdaFamily := by
  classical
  intro hA
  have h03 : ({0, 3} : Set (Fin 4)) ∈ fourPointLambdaFamily := by
    simp [fourPointLambdaFamily]
  have h01 : ({0, 1} : Set (Fin 4)) ∈ fourPointLambdaFamily := by
    simp [fourPointLambdaFamily]
  have hUnion : ({3, 0, 1} : Set (Fin 4)) ∈ fourPointLambdaFamily := by
    simpa [Set.union_assoc, Set.union_comm, Set.union_left_comm] using hA.union_mem h03 h01
  -- The union of two generators leaves the explicit six-set list.
  have hNotUnion : ({3, 0, 1} : Set (Fin 4)) ∉ fourPointLambdaFamily := by
    intro h
    have h' :
        ({3, 0, 1} : Set (Fin 4)) = ∅ ∨
          ({3, 0, 1} : Set (Fin 4)) = ({0, 1} : Set (Fin 4)) ∨
            ({3, 0, 1} : Set (Fin 4)) = ({0, 3} : Set (Fin 4)) ∨
              ({3, 0, 1} : Set (Fin 4)) = ({1, 2} : Set (Fin 4)) ∨
                ({3, 0, 1} : Set (Fin 4)) = ({2, 3} : Set (Fin 4)) ∨
                  ({3, 0, 1} : Set (Fin 4)) = (univ : Set (Fin 4)) := by
      simpa [fourPointLambdaFamily] using h
    have h0 : (0 : Fin 4) ∈ ({3, 0, 1} : Set (Fin 4)) := by simp
    have h1 : (1 : Fin 4) ∈ ({3, 0, 1} : Set (Fin 4)) := by simp
    have h3 : (3 : Fin 4) ∈ ({3, 0, 1} : Set (Fin 4)) := by simp
    have h2not : (2 : Fin 4) ∉ ({3, 0, 1} : Set (Fin 4)) := by simp
    rcases h' with h' | h' | h' | h' | h' | h'
    · have : (0 : Fin 4) ∈ (∅ : Set (Fin 4)) := by
        rw [← h']
        exact h0
      simp at this
    · have : (3 : Fin 4) ∈ ({0, 1} : Set (Fin 4)) := by
        rw [← h']
        exact h3
      simp at this
    · have : (1 : Fin 4) ∈ ({0, 3} : Set (Fin 4)) := by
        rw [← h']
        exact h1
      simp at this
    · have : (0 : Fin 4) ∈ ({1, 2} : Set (Fin 4)) := by
        rw [← h']
        exact h0
      simp at this
    · have : (0 : Fin 4) ∈ ({2, 3} : Set (Fin 4)) := by
        rw [← h']
        exact h0
      simp at this
    · have : (2 : Fin 4) ∈ ({3, 0, 1} : Set (Fin 4)) := by
        rw [h']
        simp
      exact h2not this
  exact hNotUnion hUnion

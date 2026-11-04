/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_15.ch3_sec3_15_definition_3_15_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_proposition_2_16.Circulation
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_7.ch2_sec2_7_proposition_2_16.Root

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators Matrix

section Theorem_4_11

/-- The directed arc set of the loopless complete digraph on `Fin n`. -/
abbrev tsp_arc (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≠ ij.2}

/-- The `x`-coordinate space indexed by the directed arcs of the loopless complete digraph on
`Fin n`. -/
abbrev tsp_arc_coords (n : ℕ) := tsp_arc n → ℝ

/-- The MTZ potential coordinates indexed by the vertices of `Fin n`. -/
abbrev tsp_potential_coords (n : ℕ) := Fin n → ℝ

/-- The tail of a directed arc. -/
def arc_tail {n : ℕ} (a : tsp_arc n) : Fin n :=
  a.1.1

/-- The head of a directed arc. -/
def arc_head {n : ℕ} (a : tsp_arc n) : Fin n :=
  a.1.2

/-- The arcs whose tail and head both lie in the vertex subset `S`. -/
def internal_arc_finset {n : ℕ} (S : Finset (Fin n)) : Finset (tsp_arc n) :=
  Finset.univ.filter fun a ↦ arc_tail a ∈ S ∧ arc_head a ∈ S

/-- The common degree and nonnegativity constraints used by the subtour and MTZ formulations of
the asymmetric traveling salesman problem. -/
def tsp_degree_constraints {n : ℕ} (x : tsp_arc_coords n) : Prop :=
  (∀ v : Fin n, outgoing_flow arc_tail x v = 1) ∧
    (∀ v : Fin n, incoming_flow arc_head x v = 1) ∧
      ∀ a : tsp_arc n, 0 ≤ x a

/-- The subtour-elimination polyhedron: arc-vectors satisfying the degree constraints and every
proper nonempty subtour inequality `x(A(S)) ≤ |S| - 1`. -/
def subtour_polyhedron (n : ℕ) : Set (tsp_arc_coords n) :=
  {x | tsp_degree_constraints x ∧
    ∀ S : Finset (Fin n), S.Nonempty → S.card < n →
      Finset.sum (internal_arc_finset S) x ≤ (S.card - 1 : ℝ)}

/-- Membership in `subtour_polyhedron n` is exactly the degree system together with all proper
nonempty subtour inequalities. -/
theorem mem_subtour_polyhedron_iff
    {n : ℕ}
    {x : tsp_arc_coords n} :
    x ∈ subtour_polyhedron n ↔
      tsp_degree_constraints x ∧
        ∀ S : Finset (Fin n), S.Nonempty → S.card < n →
          Finset.sum (internal_arc_finset S) x ≤ (S.card - 1 : ℝ) := by
  -- This is just the defining expansion of `subtour_polyhedron`.
  rfl

/-- The Miller-Tucker-Zemlin polyhedron: arc-vectors `x` together with vertex potentials `u`
satisfying the degree constraints, the normalization at the distinguished root, the bounds
`1 ≤ u_i ≤ n - 1` away from the root, and the MTZ arc inequalities. -/
def mtz_polyhedron {n : ℕ} (root : Fin n) : Set (tsp_arc_coords n × tsp_potential_coords n) :=
  {xu | tsp_degree_constraints xu.1 ∧
    xu.2 root = 0 ∧
      (∀ v : Fin n, v ≠ root → 1 ≤ xu.2 v ∧ xu.2 v ≤ (n - 1 : ℝ)) ∧
        ∀ a : tsp_arc n, arc_tail a ≠ root → arc_head a ≠ root →
          xu.2 (arc_tail a) - xu.2 (arc_head a) + (n : ℝ) * xu.1 a ≤ (n - 1 : ℝ)}

/-- Membership in `mtz_polyhedron root` is exactly the conjunction of the degree constraints,
the root normalization, the vertex-potential bounds, and the MTZ arc inequalities. -/
theorem mem_mtz_polyhedron_iff
    {n : ℕ}
    {root : Fin n}
    {xu : tsp_arc_coords n × tsp_potential_coords n} :
    xu ∈ mtz_polyhedron root ↔
      tsp_degree_constraints xu.1 ∧
        xu.2 root = 0 ∧
          (∀ v : Fin n, v ≠ root → 1 ≤ xu.2 v ∧ xu.2 v ≤ (n - 1 : ℝ)) ∧
            (∀ a : tsp_arc n, arc_tail a ≠ root → arc_head a ≠ root →
              xu.2 (arc_tail a) - xu.2 (arc_head a) + (n : ℝ) * xu.1 a ≤ (n - 1 : ℝ)) := by
  -- This is just the defining expansion of `mtz_polyhedron`.
  rfl

/-- Helper for Theorem 4.11: the nonroot vertices relative to the distinguished vertex `root`. -/
abbrev nonrootVertex {n : ℕ} (root : Fin n) := {v : Fin n // v ≠ root}

/-- Helper for Theorem 4.11: restrict a full MTZ potential to the nonroot vertices. -/
def restrictNonrootPotential
    {n : ℕ} (root : Fin n) (u : tsp_potential_coords n) :
    nonrootVertex root → ℝ :=
  fun v ↦ u v.1

/-- Helper for Theorem 4.11: extend a nonroot potential by setting the root potential equal to `0`.
-/
def extendNonrootPotential
    {n : ℕ} (root : Fin n) (z : nonrootVertex root → ℝ) :
    tsp_potential_coords n :=
  fun v ↦ if h : v = root then 0 else z ⟨v, h⟩

/-- Helper for Theorem 4.11: the omitted-root extension sends `root` to `0`. -/
theorem extendNonrootPotential_apply_root
    {n : ℕ} (root : Fin n) (z : nonrootVertex root → ℝ) :
    extendNonrootPotential root z root = 0 := by
  -- The defining `if` picks the normalized root branch.
  simp [extendNonrootPotential]

/-- Helper for Theorem 4.11: away from `root`, the extension agrees with the omitted-root data. -/
theorem extendNonrootPotential_apply_of_ne
    {n : ℕ} {root v : Fin n} (z : nonrootVertex root → ℝ) (hv : v ≠ root) :
    extendNonrootPotential root z v = z ⟨v, hv⟩ := by
  -- The defining `if` picks the nonroot branch.
  simp [extendNonrootPotential, hv]

/-- Helper for Theorem 4.11: restricting the extension recovers the original omitted-root
potential. -/
theorem restrictNonrootPotential_extendNonrootPotential
    {n : ℕ} (root : Fin n) (z : nonrootVertex root → ℝ) :
    restrictNonrootPotential root (extendNonrootPotential root z) = z := by
  -- Both functions agree pointwise on every nonroot vertex.
  funext v
  simp [restrictNonrootPotential, extendNonrootPotential, v.2]

/-- Helper for Theorem 4.11: the canonical arc from `root` to a nonroot vertex. -/
def rootToNonrootArc
    {n : ℕ} (root : Fin n) (v : nonrootVertex root) :
    tsp_arc n :=
  ⟨(root, v.1), fun h ↦ v.2 h.symm⟩

/-- Helper for Theorem 4.11: the canonical arc from a nonroot vertex to `root`. -/
def nonrootToRootArc
    {n : ℕ} (root : Fin n) (v : nonrootVertex root) :
    tsp_arc n :=
  ⟨(v.1, root), v.2⟩

/-- Helper for Theorem 4.11: if an arc leaves `root`, then its head is nonroot. -/
theorem arc_head_ne_root_of_tail_eq_root
    {n : ℕ} {root : Fin n} {a : tsp_arc n}
    (htail : arc_tail a = root) :
    arc_head a ≠ root := by
  -- A loopless arc cannot have both endpoints equal to `root`.
  intro hhead
  exact a.2 (htail.trans hhead.symm)

/-- Helper for Theorem 4.11: if an arc enters `root`, then its tail is nonroot. -/
theorem arc_tail_ne_root_of_head_eq_root
    {n : ℕ} {root : Fin n} {a : tsp_arc n}
    (hhead : arc_head a = root) :
    arc_tail a ≠ root := by
  -- A loopless arc cannot have both endpoints equal to `root`.
  intro htail
  exact a.2 (htail.trans hhead.symm)

/-- Helper for Theorem 4.11: the omitted-root incidence matrix whose rows are arcs and whose
columns are the nonroot vertices. -/
def augmentedMtzMatrix
    {n : ℕ} (root : Fin n) :
    Matrix (tsp_arc n) (nonrootVertex root) ℝ :=
  fun a v ↦
    (if arc_tail a = v.1 then (1 : ℝ) else 0) -
      (if arc_head a = v.1 then (1 : ℝ) else 0)

/-- Helper for Theorem 4.11: the right-hand side of the omitted-root MTZ system. Root-outgoing rows
encode `1 ≤ z`, root-incoming rows encode `z ≤ n - 1`, and the remaining rows encode the usual MTZ
arc inequalities. -/
def augmentedMtzRhs
    {n : ℕ} (root : Fin n) (x : tsp_arc_coords n) :
    tsp_arc n → ℝ :=
  fun a ↦
    if arc_tail a = root then
      (-1 : ℝ)
    else
      (n - 1 : ℝ) - if arc_head a = root then 0 else (n : ℝ) * x a

/-- Helper for Theorem 4.11: summing the tail-indicator column recovers the omitted-root extension
at the tail endpoint. -/
theorem sum_tailIndicator_mul_eq_extendNonrootPotential
    {n : ℕ} {root : Fin n}
    (z : nonrootVertex root → ℝ) (a : tsp_arc n) :
    ∑ v : nonrootVertex root, (if arc_tail a = v.1 then (1 : ℝ) else 0) * z v =
      extendNonrootPotential root z (arc_tail a) := by
  classical
  by_cases htail : arc_tail a = root
  · -- If the tail is `root`, every indicator term vanishes and so does the extension.
    have hzero : ∀ v : nonrootVertex root, arc_tail a ≠ v.1 := by
      intro v
      simpa [htail, eq_comm] using v.2
    have hsum :
        ∑ v : nonrootVertex root, (if arc_tail a = v.1 then (1 : ℝ) else 0) * z v = 0 := by
      refine Finset.sum_eq_zero ?_
      intro v hv
      simp [hzero v]
    simpa [extendNonrootPotential, htail] using hsum
  · -- If the tail is nonroot, only the matching subtype contributes to the sum.
    let vtail : nonrootVertex root := ⟨arc_tail a, htail⟩
    have hsingle :
        ∑ v : nonrootVertex root, (if arc_tail a = v.1 then (1 : ℝ) else 0) * z v = z vtail := by
      rw [Finset.sum_eq_single vtail]
      · simp [vtail]
      · intro v hv hne
        have hneq : arc_tail a ≠ v.1 := by
          intro hval
          apply hne
          exact Subtype.ext (by simpa [vtail] using hval.symm)
        simp [hneq]
      · simp [vtail]
    rw [hsingle]
    simp [extendNonrootPotential, htail, vtail]

/-- Helper for Theorem 4.11: summing the head-indicator column recovers the omitted-root extension
at the head endpoint. -/
theorem sum_headIndicator_mul_eq_extendNonrootPotential
    {n : ℕ} {root : Fin n}
    (z : nonrootVertex root → ℝ) (a : tsp_arc n) :
    ∑ v : nonrootVertex root, (if arc_head a = v.1 then (1 : ℝ) else 0) * z v =
      extendNonrootPotential root z (arc_head a) := by
  classical
  by_cases hhead : arc_head a = root
  · -- If the head is `root`, every indicator term vanishes and so does the extension.
    have hzero : ∀ v : nonrootVertex root, arc_head a ≠ v.1 := by
      intro v
      simpa [hhead, eq_comm] using v.2
    have hsum :
        ∑ v : nonrootVertex root, (if arc_head a = v.1 then (1 : ℝ) else 0) * z v = 0 := by
      refine Finset.sum_eq_zero ?_
      intro v hv
      simp [hzero v]
    simpa [extendNonrootPotential, hhead] using hsum
  · -- If the head is nonroot, only the matching subtype contributes to the sum.
    let vhead : nonrootVertex root := ⟨arc_head a, hhead⟩
    have hsingle :
        ∑ v : nonrootVertex root, (if arc_head a = v.1 then (1 : ℝ) else 0) * z v = z vhead := by
      rw [Finset.sum_eq_single vhead]
      · simp [vhead]
      · intro v hv hne
        have hneq : arc_head a ≠ v.1 := by
          intro hval
          apply hne
          exact Subtype.ext (by simpa [vhead] using hval.symm)
        simp [hneq]
      · simp [vhead]
    rw [hsingle]
    simp [extendNonrootPotential, hhead, vhead]

/-- Helper for Theorem 4.11: each row of the omitted-root incidence matrix evaluates to the
difference of the extended potentials at the tail and head endpoints. -/
theorem augmentedMtzMatrix_mulVec_apply
    {n : ℕ} {root : Fin n}
    (z : nonrootVertex root → ℝ) (a : tsp_arc n) :
    (augmentedMtzMatrix root *ᵥ z) a =
      extendNonrootPotential root z (arc_tail a) -
        extendNonrootPotential root z (arc_head a) := by
  -- Expand the row action and separate the tail and head indicator sums.
  calc
    (augmentedMtzMatrix root *ᵥ z) a
        = ∑ v : nonrootVertex root,
            ((if arc_tail a = v.1 then (1 : ℝ) else 0) -
                (if arc_head a = v.1 then (1 : ℝ) else 0)) * z v := by
            simp [augmentedMtzMatrix, Matrix.mulVec, dotProduct]
    _ = ∑ v : nonrootVertex root,
          ((if arc_tail a = v.1 then (1 : ℝ) else 0) * z v -
            (if arc_head a = v.1 then (1 : ℝ) else 0) * z v) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            rw [sub_mul]
    _ = ∑ v : nonrootVertex root, (if arc_tail a = v.1 then (1 : ℝ) else 0) * z v -
          ∑ v : nonrootVertex root, (if arc_head a = v.1 then (1 : ℝ) else 0) * z v := by
            rw [Finset.sum_sub_distrib]
    _ = extendNonrootPotential root z (arc_tail a) -
          extendNonrootPotential root z (arc_head a) := by
            rw [sum_tailIndicator_mul_eq_extendNonrootPotential,
              sum_headIndicator_mul_eq_extendNonrootPotential]

/-- Helper for Theorem 4.11: the omitted-root MTZ witness is exactly the feasibility of the native
augmented arc system. -/
theorem existsNonrootPotential_iff_augmentedMtzSystem
    {n : ℕ}
    {root : Fin n}
    {x : tsp_arc_coords n} :
    (∃ z : nonrootVertex root → ℝ,
      (∀ v : nonrootVertex root, 1 ≤ z v ∧ z v ≤ (n - 1 : ℝ)) ∧
        (∀ a : tsp_arc n, arc_tail a ≠ root → arc_head a ≠ root →
          extendNonrootPotential root z (arc_tail a) -
              extendNonrootPotential root z (arc_head a) +
                (n : ℝ) * x a ≤
            (n - 1 : ℝ))) ↔
      ∃ z : nonrootVertex root → ℝ, augmentedMtzMatrix root *ᵥ z ≤ augmentedMtzRhs root x := by
  constructor
  · rintro ⟨z, hz_bounds, hz_arcs⟩
    refine ⟨z, ?_⟩
    intro a
    -- Match each row with the corresponding MTZ bound or arc inequality.
    by_cases htail : arc_tail a = root
    · have hhead : arc_head a ≠ root := arc_head_ne_root_of_tail_eq_root htail
      let vhead : nonrootVertex root := ⟨arc_head a, hhead⟩
      have hbound : 1 ≤ z vhead := (hz_bounds vhead).1
      have hrow : -z vhead ≤ (-1 : ℝ) := by
        linarith
      simpa [augmentedMtzRhs, htail, augmentedMtzMatrix_mulVec_apply,
        extendNonrootPotential_apply_root, extendNonrootPotential_apply_of_ne, vhead, hhead] using
        hrow
    · by_cases hhead : arc_head a = root
      · let vtail : nonrootVertex root := ⟨arc_tail a, htail⟩
        have hbound : z vtail ≤ (n - 1 : ℝ) := (hz_bounds vtail).2
        simpa [augmentedMtzRhs, htail, hhead, augmentedMtzMatrix_mulVec_apply,
          extendNonrootPotential_apply_root, extendNonrootPotential_apply_of_ne, vtail] using
          hbound
      · have harc :
          extendNonrootPotential root z (arc_tail a) -
              extendNonrootPotential root z (arc_head a) ≤
            (n - 1 : ℝ) - (n : ℝ) * x a := by
          linarith [hz_arcs a htail hhead]
        simpa [augmentedMtzRhs, htail, hhead, augmentedMtzMatrix_mulVec_apply] using harc
  · rintro ⟨z, hz_system⟩
    refine ⟨z, ?_, ?_⟩
    · intro v
      -- The root-outgoing and root-incoming rows recover the lower and upper bounds.
      have hlower :=
        hz_system (rootToNonrootArc root v)
      have hupper :=
        hz_system (nonrootToRootArc root v)
      have hlower' : 1 ≤ z v := by
        have hrow :
            extendNonrootPotential root z (arc_tail (rootToNonrootArc root v)) -
                extendNonrootPotential root z (arc_head (rootToNonrootArc root v)) ≤
              augmentedMtzRhs root x (rootToNonrootArc root v) := by
          simpa [augmentedMtzMatrix_mulVec_apply] using hlower
        have htail_arc : arc_tail (rootToNonrootArc root v) = root := by
          rfl
        have hhead_arc : arc_head (rootToNonrootArc root v) = v.1 := by
          rfl
        rw [htail_arc, hhead_arc] at hrow
        rw [extendNonrootPotential_apply_root] at hrow
        have hhead_eval : extendNonrootPotential root z v.1 = z v := by
          simpa using extendNonrootPotential_apply_of_ne (root := root) (v := v.1) z v.2
        rw [hhead_eval] at hrow
        have hrhs_eval :
            augmentedMtzRhs root x (rootToNonrootArc root v) = (-1 : ℝ) := by
          simp [augmentedMtzRhs, htail_arc]
        rw [hrhs_eval] at hrow
        have hrow' : -z v ≤ (-1 : ℝ) := by
          simpa using hrow
        linarith
      have hupper' : z v ≤ (n - 1 : ℝ) := by
        have hrow :
            extendNonrootPotential root z (arc_tail (nonrootToRootArc root v)) -
                extendNonrootPotential root z (arc_head (nonrootToRootArc root v)) ≤
              augmentedMtzRhs root x (nonrootToRootArc root v) := by
          simpa [augmentedMtzMatrix_mulVec_apply] using hupper
        have htail_arc : arc_tail (nonrootToRootArc root v) = v.1 := by
          rfl
        have hhead_arc : arc_head (nonrootToRootArc root v) = root := by
          rfl
        rw [htail_arc, hhead_arc] at hrow
        have htail_eval : extendNonrootPotential root z v.1 = z v := by
          simpa using extendNonrootPotential_apply_of_ne (root := root) (v := v.1) z v.2
        rw [htail_eval, extendNonrootPotential_apply_root] at hrow
        have hrhs_eval :
            augmentedMtzRhs root x (nonrootToRootArc root v) = (n - 1 : ℝ) := by
          simp [augmentedMtzRhs, htail_arc, hhead_arc, v.2]
        rw [hrhs_eval] at hrow
        simpa using hrow
      constructor
      · exact hlower'
      · exact hupper'
    · intro a htail hhead
      -- A nonroot-to-nonroot row is exactly the standard MTZ arc inequality.
      have hrow := hz_system a
      have hrow' :
          extendNonrootPotential root z (arc_tail a) -
              extendNonrootPotential root z (arc_head a) ≤
            (n - 1 : ℝ) - (n : ℝ) * x a := by
        simpa [augmentedMtzRhs, htail, hhead, augmentedMtzMatrix_mulVec_apply] using hrow
      linarith

/-- Helper for Theorem 4.11: reindexing the native augmented MTZ system to `Fin` produces the
exact finite normal form needed for the Chapter 3 projection machinery. -/
theorem memImageFst_mtzPolyhedron_iff_finAugmentedArcSystem
    {n : ℕ}
    {root : Fin n}
    {x : tsp_arc_coords n}
    (eArc : tsp_arc n ≃ Fin (Fintype.card (tsp_arc n)))
    (ePot : nonrootVertex root ≃ Fin (Fintype.card (nonrootVertex root))) :
    x ∈ Prod.fst '' mtz_polyhedron root ↔
      tsp_degree_constraints x ∧
        ∃ z : Fin (Fintype.card (nonrootVertex root)) → ℝ,
          (augmentedMtzMatrix root).reindex eArc ePot *ᵥ z ≤
            augmentedMtzRhs root x ∘ eArc.symm := by
  rw [mem_image_fst_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_mtz_polyhedron_iff] at hu
    rcases hu with ⟨hxdeg, hroot, hbounds, harcs⟩
    have hz_native :
        ∃ z : nonrootVertex root → ℝ,
          augmentedMtzMatrix root *ᵥ z ≤ augmentedMtzRhs root x := by
      refine (existsNonrootPotential_iff_augmentedMtzSystem).mp ?_
      refine ⟨restrictNonrootPotential root u, ?_, ?_⟩
      · -- Restrict the full MTZ bounds to the nonroot coordinates.
        intro v
        exact hbounds v.1 v.2
      · -- The nonroot MTZ rows are inherited from the full witness unchanged.
        intro a htail hhead
        simpa [restrictNonrootPotential, extendNonrootPotential, htail, hhead] using
          harcs a htail hhead
    rcases hz_native with ⟨z, hz⟩
    refine ⟨hxdeg, ?_⟩
    exact (exists_solution_reindex_iff eArc ePot (augmentedMtzMatrix root)
      (augmentedMtzRhs root x)).2 ⟨z, hz⟩
  · rintro ⟨hxdeg, hz⟩
    have hz_native :
        ∃ z : nonrootVertex root → ℝ,
          augmentedMtzMatrix root *ᵥ z ≤ augmentedMtzRhs root x :=
      (exists_solution_reindex_iff eArc ePot (augmentedMtzMatrix root)
        (augmentedMtzRhs root x)).1 hz
    rw [← existsNonrootPotential_iff_augmentedMtzSystem] at hz_native
    rcases hz_native with ⟨z, hz_bounds, hz_arcs⟩
    refine ⟨extendNonrootPotential root z, ?_⟩
    rw [mem_mtz_polyhedron_iff]
    refine ⟨hxdeg, ?_, ?_, ?_⟩
    · -- The extension is normalized at the root by construction.
      exact extendNonrootPotential_apply_root root z
    · -- The omitted-root bounds reassemble into the full MTZ bounds.
      intro v hv
      simpa [extendNonrootPotential, hv] using hz_bounds ⟨v, hv⟩
    · -- The omitted-root inequalities are exactly the nonroot MTZ arc rows.
      intro a htail hhead
      exact hz_arcs a htail hhead

/-- Helper for Theorem 4.11: projecting `mtz_polyhedron root` is equivalent to keeping the degree
constraints and choosing omitted-root potentials satisfying the MTZ bounds and arc inequalities. -/
theorem mem_imageFst_mtzPolyhedron_iff_existsNonrootPotential
    {n : ℕ}
    {root : Fin n}
    {x : tsp_arc_coords n} :
    x ∈ Prod.fst '' mtz_polyhedron root ↔
      tsp_degree_constraints x ∧
        ∃ z : nonrootVertex root → ℝ,
          (∀ v : nonrootVertex root, 1 ≤ z v ∧ z v ≤ (n - 1 : ℝ)) ∧
            (∀ a : tsp_arc n, arc_tail a ≠ root → arc_head a ≠ root →
              extendNonrootPotential root z (arc_tail a) -
                  extendNonrootPotential root z (arc_head a) +
                    (n : ℝ) * x a ≤
                (n - 1 : ℝ)) := by
  rw [mem_image_fst_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [mem_mtz_polyhedron_iff] at hu
    rcases hu with ⟨hxdeg, hroot, hbounds, harcs⟩
    refine ⟨hxdeg, restrictNonrootPotential root u, ?_, ?_⟩
    · -- Restrict the full MTZ bounds to the nonroot coordinates.
      intro v
      exact hbounds v.1 v.2
    · -- The arc inequalities are already stated on the full potential and survive restriction.
      intro a htail hhead
      simpa [restrictNonrootPotential, extendNonrootPotential, htail, hhead] using
        harcs a htail hhead
  · rintro ⟨hxdeg, z, hz_bounds, hz_arcs⟩
    refine ⟨extendNonrootPotential root z, ?_⟩
    -- Package the omitted-root data back into the defining MTZ conjunction.
    rw [mem_mtz_polyhedron_iff]
    refine ⟨hxdeg, ?_, ?_, ?_⟩
    · -- The omitted-root extension is normalized by construction.
      exact extendNonrootPotential_apply_root root z
    · -- The nonroot branch of the extension inherits the stored bounds verbatim.
      intro v hv
      simpa [extendNonrootPotential, hv] using hz_bounds ⟨v, hv⟩
    · -- The same extension also restores the MTZ arc inequalities.
      intro a htail hhead
      exact hz_arcs a htail hhead

/-- Helper for Theorem 4.11: summing incoming flow over all vertices counts each arc exactly once.
-/
theorem sum_incomingFlow_eq_total
    {V A : Type*} [Fintype V] [Fintype A]
    (head : A → V) (x : A → ℝ) :
    (∑ v : V, incoming_flow head x v) = ∑ a : A, x a := by
  classical
  -- Each arc contributes to the incoming sum exactly at its head.
  change (∑ v : V, (Finset.univ.filter fun a ↦ head a = v).sum x) = ∑ a : A, x a
  calc
    (∑ v : V, (Finset.univ.filter fun a ↦ head a = v).sum x)
        = ∑ a : A, ∑ v : V, if head a = v then x a else 0 := by
            simp [Finset.sum_comm, Finset.sum_filter]
    _ = ∑ a : A, x a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp

/-- Helper for Theorem 4.11: summing outgoing flow over all vertices counts each arc exactly once.
-/
theorem sum_outgoingFlow_eq_total
    {V A : Type*} [Fintype V] [Fintype A]
    (tail : A → V) (x : A → ℝ) :
    (∑ v : V, outgoing_flow tail x v) = ∑ a : A, x a := by
  classical
  -- Each arc contributes to the outgoing sum exactly at its tail.
  change (∑ v : V, (Finset.univ.filter fun a ↦ tail a = v).sum x) = ∑ a : A, x a
  calc
    (∑ v : V, (Finset.univ.filter fun a ↦ tail a = v).sum x)
        = ∑ a : A, ∑ v : V, if tail a = v then x a else 0 := by
            simp [Finset.sum_comm, Finset.sum_filter]
    _ = ∑ a : A, x a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          simp

/-- Helper for Theorem 4.11: conservation at every nonroot vertex forces conservation at `root`.
-/
theorem nonrootBalance_implies_rootBalance
    {A : Type*} [Fintype A]
    {n : ℕ} (root : Fin n) (tail head : A → Fin n) (u : A → ℝ)
    (hbal : ∀ v : nonrootVertex root, incoming_flow head u v.1 = outgoing_flow tail u v.1) :
    incoming_flow head u root = outgoing_flow tail u root := by
  classical
  have hin_total : (∑ v : Fin n, incoming_flow head u v) = ∑ a : A, u a :=
    sum_incomingFlow_eq_total head u
  have hout_total : (∑ v : Fin n, outgoing_flow tail u v) = ∑ a : A, u a :=
    sum_outgoingFlow_eq_total tail u
  have hin_split :=
    Fintype.sum_subtype_add_sum_subtype (p := fun v : Fin n ↦ v = root)
      (fun v : Fin n ↦ incoming_flow head u v)
  have hout_split :=
    Fintype.sum_subtype_add_sum_subtype (p := fun v : Fin n ↦ v = root)
      (fun v : Fin n ↦ outgoing_flow tail u v)
  rw [hin_total] at hin_split
  rw [hout_total] at hout_split
  have hin_split' :
      incoming_flow head u root +
        ∑ v : {v : Fin n // v ≠ root}, incoming_flow head u v.1 = ∑ a : A, u a := by
    simpa using hin_split
  have hout_split' :
      outgoing_flow tail u root +
        ∑ v : {v : Fin n // v ≠ root}, outgoing_flow tail u v.1 = ∑ a : A, u a := by
    simpa using hout_split
  have hnonroot :
      ∑ v : {v : Fin n // v ≠ root}, incoming_flow head u v.1 =
        ∑ v : {v : Fin n // v ≠ root}, outgoing_flow tail u v.1 := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    exact hbal v
  calc
    incoming_flow head u root = ∑ a : A, u a -
        ∑ v : {v : Fin n // v ≠ root}, incoming_flow head u v.1 := by
          linarith [hin_split']
    _ = ∑ a : A, u a -
        ∑ v : {v : Fin n // v ≠ root}, outgoing_flow tail u v.1 := by
          rw [hnonroot]
    _ = outgoing_flow tail u root := by
          linarith [hout_split']

/-- Helper for Theorem 4.11: summing a tail-indicator against an arc vector recovers the outgoing
flow at that vertex. -/
theorem sum_mul_tailIndicator_eq_outgoingFlow
    {n : ℕ} {root : Fin n}
    (u : tsp_arc_coords n) (v : nonrootVertex root) :
    ∑ a : tsp_arc n, u a * (if arc_tail a = v.1 then (1 : ℝ) else 0) =
      outgoing_flow arc_tail u v.1 := by
  -- Expanding `outgoing_flow` turns the indicator-weighted total into the filtered outgoing sum.
  simp [outgoing_flow, Finset.sum_filter]

/-- Helper for Theorem 4.11: summing a head-indicator against an arc vector recovers the incoming
flow at that vertex. -/
theorem sum_mul_headIndicator_eq_incomingFlow
    {n : ℕ} {root : Fin n}
    (u : tsp_arc_coords n) (v : nonrootVertex root) :
    ∑ a : tsp_arc n, u a * (if arc_head a = v.1 then (1 : ℝ) else 0) =
      incoming_flow arc_head u v.1 := by
  -- Expanding `incoming_flow` turns the indicator-weighted total into the filtered incoming sum.
  simp [incoming_flow, Finset.sum_filter]

/-- Helper for Theorem 4.11: the native Farkas annihilation equation for the augmented MTZ matrix
is exactly nonroot flow balance on the arc multipliers. -/
theorem annihilatesAugmentedMtzMatrixIffNonrootBalance
    {n : ℕ} {root : Fin n} {u : tsp_arc_coords n} :
    u ᵥ* augmentedMtzMatrix root = 0 ↔
      ∀ v : nonrootVertex root, incoming_flow arc_head u v.1 = outgoing_flow arc_tail u v.1 := by
  constructor
  · intro hu v
    -- Read the zero column equation as outgoing minus incoming flow at the chosen nonroot vertex.
    have hv : (u ᵥ* augmentedMtzMatrix root) v = 0 := congrFun hu v
    have hcolumn :
        (u ᵥ* augmentedMtzMatrix root) v =
          outgoing_flow arc_tail u v.1 - incoming_flow arc_head u v.1 := by
      calc
        (u ᵥ* augmentedMtzMatrix root) v
            = ∑ a : tsp_arc n,
                u a *
                  (((if arc_tail a = v.1 then (1 : ℝ) else 0) -
                      (if arc_head a = v.1 then (1 : ℝ) else 0))) := by
                simp [Matrix.vecMul, dotProduct, augmentedMtzMatrix]
        _ = ∑ a : tsp_arc n,
              (u a * (if arc_tail a = v.1 then (1 : ℝ) else 0) -
                u a * (if arc_head a = v.1 then (1 : ℝ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
        _ = (∑ a : tsp_arc n, u a * (if arc_tail a = v.1 then (1 : ℝ) else 0)) -
              ∑ a : tsp_arc n, u a * (if arc_head a = v.1 then (1 : ℝ) else 0) := by
              rw [Finset.sum_sub_distrib]
        _ = outgoing_flow arc_tail u v.1 - incoming_flow arc_head u v.1 := by
              rw [sum_mul_tailIndicator_eq_outgoingFlow, sum_mul_headIndicator_eq_incomingFlow]
    rw [hcolumn] at hv
    linarith
  · intro hbal
    ext v
    -- Conversely, the nonroot balance equations rewrite each column evaluation to zero.
    have hcolumn :
        (u ᵥ* augmentedMtzMatrix root) v =
          outgoing_flow arc_tail u v.1 - incoming_flow arc_head u v.1 := by
      calc
        (u ᵥ* augmentedMtzMatrix root) v
            = ∑ a : tsp_arc n,
                u a *
                  (((if arc_tail a = v.1 then (1 : ℝ) else 0) -
                      (if arc_head a = v.1 then (1 : ℝ) else 0))) := by
                simp [Matrix.vecMul, dotProduct, augmentedMtzMatrix]
        _ = ∑ a : tsp_arc n,
              (u a * (if arc_tail a = v.1 then (1 : ℝ) else 0) -
                u a * (if arc_head a = v.1 then (1 : ℝ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
        _ = (∑ a : tsp_arc n, u a * (if arc_tail a = v.1 then (1 : ℝ) else 0)) -
              ∑ a : tsp_arc n, u a * (if arc_head a = v.1 then (1 : ℝ) else 0) := by
              rw [Finset.sum_sub_distrib]
        _ = outgoing_flow arc_tail u v.1 - incoming_flow arc_head u v.1 := by
              rw [sum_mul_tailIndicator_eq_outgoingFlow, sum_mul_headIndicator_eq_incomingFlow]
    rw [hcolumn]
    calc
      outgoing_flow arc_tail u v.1 - incoming_flow arc_head u v.1
          = outgoing_flow arc_tail u v.1 - outgoing_flow arc_tail u v.1 := by
              rw [hbal v]
      _ = 0 := by ring

/-- Helper for Theorem 4.11: a nonnegative multiplier annihilating the augmented MTZ matrix is a
circulation on the complete loopless digraph. -/
theorem mem_circulationCone_of_annihilatesAugmentedMtzMatrix
    {n : ℕ} {root : Fin n} {u : tsp_arc_coords n}
    (hu_nonneg : 0 ≤ u) (hu_ann : u ᵥ* augmentedMtzMatrix root = 0) :
    u ∈ circulation_cone arc_tail arc_head := by
  -- The annihilation equations give nonroot balance, and the root balance follows by total-flow
  -- conservation.
  rw [mem_circulation_cone_iff, isCirculation_iff]
  refine ⟨?_, ?_⟩
  · intro v
    by_cases hv : v = root
    · simpa [hv] using
        nonrootBalance_implies_rootBalance (root := root) arc_tail arc_head u
          ((annihilatesAugmentedMtzMatrixIffNonrootBalance).1 hu_ann)
    · exact (annihilatesAugmentedMtzMatrixIffNonrootBalance).1 hu_ann ⟨v, hv⟩
  · intro a
    exact hu_nonneg a

/-- Helper for Theorem 4.11: a simple circuit has as many arcs as incident vertices. -/
theorem simpleCircuit_card_eq_cardVertices
    {V A : Type*} {tail head : A → V} {C : Finset A}
    (hC : IsSimpleCircuit tail head C) :
    C.card = (circuit_vertices tail head C).card := by
  classical
  have hsubset :
      circuit_vertices tail head C ⊆ C.image head := by
    intro v hv
    have hv' : v ∈ circuit_vertex_set tail head C :=
      (mem_circuit_vertices_iff tail head C v).1 hv
    rcases existsUnique_incomingArc_of_isSimpleCircuit hC v hv' with ⟨a, ha, _⟩
    exact Finset.mem_image.mpr ⟨a, ha.1, ha.2⟩
  have hsuperset :
      C.image head ⊆ circuit_vertices tail head C := by
    intro v hv
    exact Finset.mem_union.mpr (Or.inr hv)
  have hEq : circuit_vertices tail head C = C.image head :=
    Finset.Subset.antisymm hsubset hsuperset
  have hinj : Set.InjOn head (↑C : Set A) := by
    intro a ha b hb hab
    have hva : head a ∈ circuit_vertex_set tail head C := by
      exact ⟨a, ha, Or.inr rfl⟩
    rcases existsUnique_incomingArc_of_isSimpleCircuit hC (head a) hva with ⟨c, hc, huniq⟩
    have ha' : a ∈ C ∧ head a = head a := ⟨ha, rfl⟩
    have hb' : b ∈ C ∧ head b = head a := ⟨hb, hab.symm⟩
    calc
      a = c := huniq a ha'
      _ = b := (huniq b hb').symm
  rw [hEq]
  exact (Finset.card_image_iff.mpr hinj).symm

/-- Helper for Theorem 4.11: pairing a circuit characteristic vector with any weight vector
reduces to summing those weights over the circuit arcs. -/
theorem circuitCharacteristicVector_dot_eq_sum
    {A : Type*} [Fintype A]
    (C : Finset A) (d : A → ℝ) :
    circuit_characteristic_vector C ⬝ᵥ d = Finset.sum C d := by
  classical
  -- The characteristic vector is `1` on `C` and `0` off `C`, so only circuit arcs survive.
  simp [dotProduct, circuit_characteristic_vector_apply, Finset.sum_filter]

/-- Helper for Theorem 4.11: if `root` lies on a simple circuit, exactly one circuit arc leaves
`root`. -/
theorem simpleCircuit_outgoingRootArc_card_one
    {n : ℕ} {root : Fin n} {C : Finset (tsp_arc n)}
    (hC : IsSimpleCircuit arc_tail arc_head C)
    (hroot : root ∈ circuit_vertex_set arc_tail arc_head C) :
    outgoing_arc_count arc_tail C root = 1 := by
  -- This is the outgoing half of the one-in-one-out condition at `root`.
  exact (hC.one_in_one_out root hroot).2

/-- Helper for Theorem 4.11: if `root` lies on a simple circuit, exactly one circuit arc enters
`root`. -/
theorem simpleCircuit_incomingRootArc_card_one
    {n : ℕ} {root : Fin n} {C : Finset (tsp_arc n)}
    (hC : IsSimpleCircuit arc_tail arc_head C)
    (hroot : root ∈ circuit_vertex_set arc_tail arc_head C) :
    incoming_arc_count arc_head C root = 1 := by
  -- This is the incoming half of the one-in-one-out condition at `root`.
  exact (hC.one_in_one_out root hroot).1

/-- Helper for Theorem 4.11: a root-free simple circuit satisfies the augmented MTZ right-hand-side
inequality at every subtour-feasible point. -/
theorem simpleCircuit_augmentedMtzRhs_nonneg_rootFree
    {n : ℕ} {root : Fin n} {x : tsp_arc_coords n} {C : Finset (tsp_arc n)}
    (hx : x ∈ subtour_polyhedron n)
    (hC : IsSimpleCircuit arc_tail arc_head C)
    (hroot : root ∉ circuit_vertex_set arc_tail arc_head C) :
    0 ≤ circuit_characteristic_vector C ⬝ᵥ augmentedMtzRhs root x := by
  classical
  let S : Finset (Fin n) := circuit_vertices arc_tail arc_head C
  have hx_nonneg : ∀ a : tsp_arc n, 0 ≤ x a := (mem_subtour_polyhedron_iff.mp hx).1.2.2
  have hsubtour :=
    (mem_subtour_polyhedron_iff.mp hx).2
  have hS_nonempty : S.Nonempty := by
    -- A simple circuit has an arc, so its vertex set is nonempty.
    rcases hC.nonempty with ⟨a, ha⟩
    refine ⟨arc_tail a, ?_⟩
    exact (mem_circuit_vertices_iff arc_tail arc_head C (arc_tail a)).2 ⟨a, ha, Or.inl rfl⟩
  have hroot_not_mem_S : root ∉ S := by
    -- The root-free hypothesis transfers from the set-valued to the finset-valued vertex set.
    intro hmem
    exact hroot ((mem_circuit_vertices_iff arc_tail arc_head C root).1 hmem)
  have hS_card_lt : S.card < n := by
    -- Missing the root forces the circuit vertex set to be a proper subset of `Fin n`.
    simpa [S] using Finset.card_lt_univ_of_notMem hroot_not_mem_S
  have hC_subset_internal : C ⊆ internal_arc_finset S := by
    intro a ha
    -- Every circuit arc has both endpoints in the circuit vertex set.
    have htail_mem : arc_tail a ∈ S := by
      exact (mem_circuit_vertices_iff arc_tail arc_head C (arc_tail a)).2 ⟨a, ha, Or.inl rfl⟩
    have hhead_mem : arc_head a ∈ S := by
      exact (mem_circuit_vertices_iff arc_tail arc_head C (arc_head a)).2 ⟨a, ha, Or.inr rfl⟩
    simp [internal_arc_finset, S, ha, htail_mem, hhead_mem]
  have hsum_le_internal :
      Finset.sum C x ≤ Finset.sum (internal_arc_finset S) x := by
    -- Nonnegativity lets us enlarge the circuit sum to the whole internal-arc set of `S`.
    simpa using Finset.sum_le_sum_of_subset_of_nonneg hC_subset_internal
      (by
        intro a ha_internal ha_not_mem
        exact hx_nonneg a)
  have hsum_le_card :
      Finset.sum C x ≤ (S.card - 1 : ℝ) := by
    -- Apply the subtour inequality on the circuit vertex set.
    exact le_trans hsum_le_internal (hsubtour S hS_nonempty hS_card_lt)
  have hcard : C.card = S.card := by
    -- A simple circuit has as many arcs as incident vertices.
    simpa [S] using simpleCircuit_card_eq_cardVertices hC
  have hroot_free_row :
      Finset.sum C (augmentedMtzRhs root x) =
        (C.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * Finset.sum C x := by
    -- On a root-free circuit, every row is a nonroot-to-nonroot MTZ row.
    calc
      Finset.sum C (augmentedMtzRhs root x)
          = Finset.sum C (fun a ↦ ((n - 1 : ℝ) - (n : ℝ) * x a)) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              have htail_ne : arc_tail a ≠ root := by
                intro htail
                exact hroot ⟨a, ha, Or.inl htail⟩
              have hhead_ne : arc_head a ≠ root := by
                intro hhead
                exact hroot ⟨a, ha, Or.inr hhead⟩
              simp [augmentedMtzRhs, htail_ne, hhead_ne]
      _ = Finset.sum C (fun _a ↦ (n - 1 : ℝ)) - Finset.sum C (fun a ↦ (n : ℝ) * x a) := by
            rw [Finset.sum_sub_distrib]
      _ = (C.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * Finset.sum C x := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hcard_real : (C.card : ℝ) = (S.card : ℝ) := by
    exact_mod_cast hcard
  have hS_card_le_n : (S.card : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.le_of_lt hS_card_lt
  -- Combine the subtour bound with the circuit cardinality identity.
  rw [circuitCharacteristicVector_dot_eq_sum, hroot_free_row]
  rw [hcard_real]
  have hscaled_sum :
      (n : ℝ) * Finset.sum C x ≤ (n : ℝ) * ((S.card - 1 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hsum_le_card (by positivity)
  have hbaseline : 0 ≤ (n : ℝ) - (S.card : ℝ) := by
    linarith
  calc
    0 ≤ (n : ℝ) - (S.card : ℝ) := hbaseline
    _ = (S.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * ((S.card - 1 : ℝ)) := by
          ring
    _ ≤ (S.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * Finset.sum C x := by
          linarith

/-- Helper for Theorem 4.11: a simple circuit through `root` also satisfies the augmented MTZ
right-hand-side inequality at every subtour-feasible point. -/
theorem simpleCircuit_augmentedMtzRhs_nonneg_rootThrough
    {n : ℕ} {root : Fin n} {x : tsp_arc_coords n} {C : Finset (tsp_arc n)}
    (hx : x ∈ subtour_polyhedron n)
    (hC : IsSimpleCircuit arc_tail arc_head C)
    (hroot : root ∈ circuit_vertex_set arc_tail arc_head C) :
    0 ≤ circuit_characteristic_vector C ⬝ᵥ augmentedMtzRhs root x := by
  classical
  obtain ⟨outArc, hout_spec, hout_unique⟩ :=
    existsUnique_outgoingArc_of_isSimpleCircuit hC root hroot
  obtain ⟨inArc, hin_spec, hin_unique⟩ :=
    existsUnique_incomingArc_of_isSimpleCircuit hC root hroot
  let S : Finset (Fin n) := circuit_vertices arc_tail arc_head C
  let T : Finset (Fin n) := S.erase root
  let R : Finset (tsp_arc n) := (C.erase outArc).erase inArc
  have hout_mem : outArc ∈ C := hout_spec.1
  have hout_tail : arc_tail outArc = root := hout_spec.2
  have hin_mem : inArc ∈ C := hin_spec.1
  have hin_head : arc_head inArc = root := hin_spec.2
  have hroot_mem_S : root ∈ S := by
    -- Transfer the root-incidence hypothesis from the set-valued to the finset-valued vertex set.
    exact (mem_circuit_vertices_iff arc_tail arc_head C root).2 hroot
  have hout_head_ne : arc_head outArc ≠ root := arc_head_ne_root_of_tail_eq_root hout_tail
  have hin_tail_ne : arc_tail inArc ≠ root := arc_tail_ne_root_of_head_eq_root hin_head
  have hout_ne_in : outArc ≠ inArc := by
    -- The unique outgoing and incoming root arcs cannot coincide in a loopless digraph.
    intro hEq
    have hhead_out : arc_head outArc = root := by simpa [hEq] using hin_head
    exact hout_head_ne hhead_out
  have hin_mem_erase_out : inArc ∈ C.erase outArc := by
    exact Finset.mem_erase.mpr ⟨fun hEq ↦ hout_ne_in hEq.symm, hin_mem⟩
  have hT_nonempty : T.Nonempty := by
    -- The head of the root-outgoing circuit arc is a nonroot vertex on the circuit.
    refine ⟨arc_head outArc, ?_⟩
    have hhead_mem_S : arc_head outArc ∈ S := by
      exact (mem_circuit_vertices_iff arc_tail arc_head C (arc_head outArc)).2
        ⟨outArc, hout_mem, Or.inr rfl⟩
    exact Finset.mem_erase.mpr ⟨hout_head_ne, hhead_mem_S⟩
  have hT_card_lt : T.card < n := by
    -- Erasing `root` from the circuit vertex set makes it a proper subset of `Fin n`.
    have hroot_not_mem_T : root ∉ T := by
      simp [T]
    simpa using Finset.card_lt_univ_of_notMem (s := T) hroot_not_mem_T
  have hx_nonneg : ∀ a : tsp_arc n, 0 ≤ x a := (mem_subtour_polyhedron_iff.mp hx).1.2.2
  have hsubtour := (mem_subtour_polyhedron_iff.mp hx).2
  have hR_memC : ∀ a : tsp_arc n, a ∈ R → a ∈ C := by
    intro a haR
    have haR_out : a ∈ C.erase outArc := (Finset.mem_erase.mp haR).2
    exact (Finset.mem_erase.mp haR_out).2
  have hR_endpoints_nonroot :
      ∀ a : tsp_arc n, a ∈ R → arc_tail a ≠ root ∧ arc_head a ≠ root := by
    intro a haR
    have ha_ne_in : a ≠ inArc := (Finset.mem_erase.mp haR).1
    have haR_out : a ∈ C.erase outArc := (Finset.mem_erase.mp haR).2
    have ha_ne_out : a ≠ outArc := (Finset.mem_erase.mp haR_out).1
    have haC : a ∈ C := (Finset.mem_erase.mp haR_out).2
    constructor
    · -- Any remaining arc with tail `root` would be the unique outgoing root arc.
      intro htail
      exact ha_ne_out (hout_unique a ⟨haC, htail⟩)
    · -- Any remaining arc with head `root` would be the unique incoming root arc.
      intro hhead
      exact ha_ne_in (hin_unique a ⟨haC, hhead⟩)
  have hR_subset_internal : R ⊆ internal_arc_finset T := by
    intro a haR
    have haC : a ∈ C := hR_memC a haR
    have htail_mem_S : arc_tail a ∈ S := by
      exact (mem_circuit_vertices_iff arc_tail arc_head C (arc_tail a)).2 ⟨a, haC, Or.inl rfl⟩
    have hhead_mem_S : arc_head a ∈ S := by
      exact (mem_circuit_vertices_iff arc_tail arc_head C (arc_head a)).2 ⟨a, haC, Or.inr rfl⟩
    rcases hR_endpoints_nonroot a haR with ⟨htail_ne, hhead_ne⟩
    -- After removing the root, the remainder arcs are exactly internal to `T`.
    simp [internal_arc_finset, T, htail_mem_S, hhead_mem_S, htail_ne, hhead_ne]
  have hsum_remainder_le_internal :
      Finset.sum R x ≤ Finset.sum (internal_arc_finset T) x := by
    -- Nonnegativity lets us enlarge the remainder sum to all internal arcs of `T`.
    simpa using Finset.sum_le_sum_of_subset_of_nonneg hR_subset_internal
      (by
        intro a ha_internal ha_not_mem
        exact hx_nonneg a)
  have hsum_remainder_le_card :
      Finset.sum R x ≤ (T.card - 1 : ℝ) := by
    -- Apply the subtour inequality on the nonroot circuit vertices.
    exact le_trans hsum_remainder_le_internal (hsubtour T hT_nonempty hT_card_lt)
  have hC_card_succ : C.card = T.card + 1 := by
    -- A simple circuit has one more incident vertex before removing the root.
    have hcardS : C.card = S.card := by
      simpa [S] using simpleCircuit_card_eq_cardVertices hC
    have hS_card : T.card + 1 = S.card := by
      simpa [T] using (Finset.card_erase_add_one hroot_mem_S)
    calc
      C.card = S.card := hcardS
      _ = T.card + 1 := hS_card.symm
  have hR_card_plus_two : R.card + 2 = C.card := by
    -- The remainder is obtained by erasing the unique outgoing and incoming root arcs.
    have hR_card : R.card + 1 = (C.erase outArc).card := by
      simpa [R] using (Finset.card_erase_add_one hin_mem_erase_out)
    have hErase_card : (C.erase outArc).card + 1 = C.card := by
      simpa using (Finset.card_erase_add_one hout_mem)
    calc
      R.card + 2 = (R.card + 1) + 1 := by simp [Nat.add_assoc]
      _ = (C.erase outArc).card + 1 := by rw [hR_card]
      _ = C.card := hErase_card
  have hR_card_succ : R.card + 1 = T.card := by
    have hsucc : Nat.succ (R.card + 1) = Nat.succ T.card := by
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hR_card_plus_two.trans hC_card_succ
    exact Nat.succ.inj hsucc
  have hsum_partition :
      Finset.sum C (augmentedMtzRhs root x) =
        augmentedMtzRhs root x outArc + augmentedMtzRhs root x inArc +
          Finset.sum R (augmentedMtzRhs root x) := by
    -- Split the circuit sum into the two root-incident arcs and the nonroot remainder.
    dsimp [R]
    rw [← Finset.add_sum_erase (s := C) (f := augmentedMtzRhs root x) hout_mem]
    rw [← Finset.add_sum_erase (s := C.erase outArc) (f := augmentedMtzRhs root x) hin_mem_erase_out]
    ring
  have hout_row : augmentedMtzRhs root x outArc = (-1 : ℝ) := by
    -- The outgoing root row is exactly the lower-bound row.
    simp [augmentedMtzRhs, hout_tail]
  have hin_row : augmentedMtzRhs root x inArc = (n - 1 : ℝ) := by
    -- The incoming root row is exactly the upper-bound row.
    simp [augmentedMtzRhs, hin_head, hin_tail_ne]
  have hsum_remainder_rows :
      Finset.sum R (augmentedMtzRhs root x) =
        (R.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * Finset.sum R x := by
    -- Every remaining arc is nonroot-to-nonroot, so each row is a standard MTZ arc row.
    calc
      Finset.sum R (augmentedMtzRhs root x)
          = Finset.sum R (fun a ↦ ((n - 1 : ℝ) - (n : ℝ) * x a)) := by
              refine Finset.sum_congr rfl ?_
              intro a haR
              rcases hR_endpoints_nonroot a haR with ⟨htail_ne, hhead_ne⟩
              simp [augmentedMtzRhs, htail_ne, hhead_ne]
      _ = Finset.sum R (fun _a ↦ (n - 1 : ℝ)) - Finset.sum R (fun a ↦ (n : ℝ) * x a) := by
            rw [Finset.sum_sub_distrib]
      _ = (R.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * Finset.sum R x := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.mul_sum]
  have hR_card_real : (R.card : ℝ) + 1 = (T.card : ℝ) := by
    exact_mod_cast hR_card_succ
  have htotal_rewrite :
      (-1 : ℝ) + (n - 1 : ℝ) + ((R.card : ℝ) * (n - 1 : ℝ) - (n : ℝ) * Finset.sum R x) =
        (T.card : ℝ) * (n - 1 : ℝ) - 1 - (n : ℝ) * Finset.sum R x := by
    have hR_card_eq : (R.card : ℝ) = (T.card : ℝ) - 1 := by
      linarith
    rw [hR_card_eq]
    ring
  have hn_nonneg : 0 ≤ (n : ℝ) := by
    exact_mod_cast Nat.zero_le n
  have hscaled_sum :
      (n : ℝ) * Finset.sum R x ≤ (n : ℝ) * ((T.card - 1 : ℝ)) := by
    exact mul_le_mul_of_nonneg_left hsum_remainder_le_card hn_nonneg
  have hT_card_le_real : (T.card : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hT_card_lt
  have hbaseline : 0 ≤ (n : ℝ) - (T.card : ℝ) - 1 := by
    linarith
  -- Combine the root-arc decomposition with the subtour bound on the nonroot remainder.
  rw [circuitCharacteristicVector_dot_eq_sum, hsum_partition, hout_row, hin_row, hsum_remainder_rows]
  rw [htotal_rewrite]
  calc
    0 ≤ (n : ℝ) - (T.card : ℝ) - 1 := hbaseline
    _ = (T.card : ℝ) * (n - 1 : ℝ) - 1 - (n : ℝ) * ((T.card - 1 : ℝ)) := by
          ring
    _ ≤ (T.card : ℝ) * (n - 1 : ℝ) - 1 - (n : ℝ) * Finset.sum R x := by
          linarith

/-- Helper for Theorem 4.11: every simple circuit evaluates nonnegatively on the augmented MTZ
right-hand side of a subtour-feasible point. -/
theorem simpleCircuit_augmentedMtzRhs_nonneg_of_memSubtour
    {n : ℕ} {root : Fin n} {x : tsp_arc_coords n} {C : Finset (tsp_arc n)}
    (hx : x ∈ subtour_polyhedron n)
    (hC : IsSimpleCircuit arc_tail arc_head C) :
    0 ≤ circuit_characteristic_vector C ⬝ᵥ augmentedMtzRhs root x := by
  -- Split on whether the distinguished root lies on the circuit, then use the matching circuit
  -- estimate proved above.
  by_cases hroot : root ∈ circuit_vertex_set arc_tail arc_head C
  · exact simpleCircuit_augmentedMtzRhs_nonneg_rootThrough hx hC hroot
  · exact simpleCircuit_augmentedMtzRhs_nonneg_rootFree hx hC hroot

section

variable {V A : Type*} [Fintype A]

noncomputable local instance : DecidableEq A := Classical.decEq A
noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Helper for Theorem 4.11: a list of arcs is a directed walk from `u` to `v` when consecutive
arc endpoints match, starting at `u` and ending at `v`. -/
private def IsDirectedWalkFromTo (tail head : A → V) : V → V → List A → Prop
  | u, v, [] => u = v
  | u, v, a :: p => tail a = u ∧ IsDirectedWalkFromTo tail head (head a) v p

/-- Helper for Theorem 4.11: the ordered vertex list visited by a directed walk. -/
private def walkVerticesFrom (head : A → V) (u : V) : List A → List V
  | [] => [u]
  | a :: p => u :: walkVerticesFrom head (head a) p

/-- Helper for Theorem 4.11: the visited vertices of a walk are the start vertex followed by the
heads of the traversed arcs. -/
private theorem walkVerticesFrom_eq_start_cons_map_head
    {head : A → V} (u : V) (p : List A) :
    walkVerticesFrom head u p = u :: p.map head := by
  induction p generalizing u with
  | nil =>
      simp [walkVerticesFrom]
  | cons a p ih =>
      simp [walkVerticesFrom, ih]

/-- Helper for Theorem 4.11: the tail of the visited-vertex list is exactly the head list of the
walk arcs. -/
private theorem walkVerticesFrom_tail_eq_map_head
    {head : A → V} (u : V) (p : List A) :
    (walkVerticesFrom head u p).tail = p.map head := by
  simp [walkVerticesFrom_eq_start_cons_map_head]

/-- Helper for Theorem 4.11: every arc of a walk contributes its tail vertex to the visited-vertex
list. -/
private theorem tail_mem_walkVerticesFrom_of_mem
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      ∀ {a : A}, a ∈ p → tail a ∈ walkVerticesFrom head u p
  | _, _, [], hwalk, _, hmem => by
      cases hmem
  | u, v, b :: p, hwalk, a, hmem => by
      rcases hwalk with ⟨hbu, hp⟩
      -- Split according to whether `a` is the first arc or lies in the tail walk.
      rw [walkVerticesFrom]
      rcases List.mem_cons.mp hmem with rfl | hmemTail
      · simp [hbu]
      · exact List.mem_cons_of_mem _ (tail_mem_walkVerticesFrom_of_mem hp hmemTail)

/-- Helper for Theorem 4.11: every arc of a walk contributes its head vertex to the tail of the
visited-vertex list. -/
private theorem head_mem_walkVerticesTail_of_mem
    {head : A → V} (u : V) {p : List A} {a : A} (ha : a ∈ p) :
    head a ∈ (walkVerticesFrom head u p).tail := by
  rw [walkVerticesFrom_tail_eq_map_head]
  exact List.mem_map.mpr ⟨a, ha, rfl⟩

/-- Helper for Theorem 4.11: concatenating directed walks with a matching intermediate endpoint
produces the evident longer walk. -/
private theorem directedWalk_append
    {tail head : A → V} :
    ∀ {u w v : V} {p q : List A},
      IsDirectedWalkFromTo tail head u w p →
        IsDirectedWalkFromTo tail head w v q →
          IsDirectedWalkFromTo tail head u v (p ++ q)
  | _, _, _, [], q, hp, hq => by
      -- The empty prefix contributes no arcs.
      subst hp
      simpa using hq
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      -- Keep the first arc and append recursively to the tail walk.
      exact ⟨hau, directedWalk_append hpTail hq⟩

/-- Helper for Theorem 4.11: splitting a walk at a visited vertex yields compatible prefix and
suffix walks. -/
private theorem directedWalk_split_at_visited_vertex
    {tail head : A → V} :
    ∀ {u v w : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      w ∈ walkVerticesFrom head u p →
        ∃ p₁ p₂, p = p₁ ++ p₂ ∧
          IsDirectedWalkFromTo tail head u w p₁ ∧
            IsDirectedWalkFromTo tail head w v p₂
  | u, v, w, [], hp, hw => by
      subst hp
      have hwu : w = u := by
        simpa [walkVerticesFrom] using hw
      subst hwu
      -- The empty walk visits only its start/end vertex.
      refine ⟨[], [], rfl, rfl, rfl⟩
  | u, v, w, a :: p, hp, hw => by
      rcases hp with ⟨hau, hpTail⟩
      rw [walkVerticesFrom] at hw
      rcases List.mem_cons.mp hw with rfl | hwTail
      · -- Splitting at the initial vertex leaves the whole walk in the suffix.
        refine ⟨[], a :: p, by simp, rfl, ?_⟩
        exact ⟨hau, hpTail⟩
      · rcases directedWalk_split_at_visited_vertex hpTail hwTail with
          ⟨p₁, p₂, hpSplit, hp₁, hp₂⟩
        -- Otherwise split the tail walk recursively and restore the first arc.
        refine ⟨a :: p₁, p₂, ?_, ?_, hp₂⟩
        · simp [hpSplit]
        · exact ⟨hau, by simpa [hpSplit] using hp₁⟩

/-- Helper for Theorem 4.11: visited vertices of appended walks concatenate as expected. -/
private theorem walkVerticesFrom_append
    {tail head : A → V} :
    ∀ {u w v : V} {p q : List A},
      IsDirectedWalkFromTo tail head u w p →
        IsDirectedWalkFromTo tail head w v q →
          walkVerticesFrom head u (p ++ q) =
            walkVerticesFrom head u p ++ (walkVerticesFrom head w q).tail
  | _, _, _, [], q, hp, hq => by
      subst hp
      cases q with
      | nil =>
          simp [walkVerticesFrom]
      | cons a q =>
          simp [walkVerticesFrom]
  | u, w, v, a :: p, q, hp, hq => by
      rcases hp with ⟨hau, hpTail⟩
      -- Peel off the leading arc and apply the append formula recursively to the tail walk.
      simp [walkVerticesFrom, walkVerticesFrom_append hpTail hq]

/-- Helper for Theorem 4.11: the endpoint of a directed walk appears in its visited-vertex list.
-/
private theorem terminalVertex_mem_walkVerticesFrom
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      v ∈ walkVerticesFrom head u p
  | _, _, [], hp => by
      subst hp
      simp [walkVerticesFrom]
  | u, v, a :: p, hp => by
      rcases hp with ⟨hau, hpTail⟩
      -- The endpoint of the tail walk is still the endpoint of the whole walk.
      simp [walkVerticesFrom, terminalVertex_mem_walkVerticesFrom hpTail]

/-- Helper for Theorem 4.11: if the visited vertices of a walk are nodup, then so are the walk
arcs. -/
private theorem directedWalk_nodup_of_verticesNodup
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      (walkVerticesFrom head u p).Nodup → p.Nodup
  | _, _, [], _, _ => by
      simp
  | u, v, a :: p, hp, hverts => by
      rcases hp with ⟨hau, hpTail⟩
      rw [walkVerticesFrom] at hverts
      rcases List.nodup_cons.mp hverts with ⟨hu_not_mem, htailVerts⟩
      have hpNodup := directedWalk_nodup_of_verticesNodup hpTail htailVerts
      have ha_not_mem : a ∉ p := by
        intro hmem
        -- Reusing `a` would revisit the tail vertex `u` later in the walk.
        have htailMem : tail a ∈ walkVerticesFrom head (head a) p :=
          tail_mem_walkVerticesFrom_of_mem hpTail hmem
        have huMem : u ∈ walkVerticesFrom head (head a) p := by
          simpa [hau] using htailMem
        exact hu_not_mem huMem
      exact List.nodup_cons.mpr ⟨ha_not_mem, hpNodup⟩

/-- Helper for Theorem 4.11: the final arc of a nonempty directed walk is a positive incoming arc
at the endpoint whenever every traversed arc is positive. -/
private theorem exists_positive_incoming_arc_at_walkEndpoint
    {tail head : A → V} {y : A → ℝ} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      p ≠ [] →
        (∀ b ∈ p.toFinset, 0 < y b) →
          ∃ a, a ∈ p.toFinset ∧ head a = v ∧ 0 < y a
  | _, _, [], _, hne, _ => by
      exact False.elim (hne rfl)
  | u, v, a :: p, hp, _, hpos => by
      rcases hp with ⟨hau, hpTail⟩
      by_cases hpnil : p = []
      · subst hpnil
        refine ⟨a, by simp, ?_, hpos a (by simp)⟩
        simpa using hpTail
      · have hposTail : ∀ b ∈ p.toFinset, 0 < y b := by
          intro b hb
          exact hpos b (by simpa using List.mem_cons_of_mem a (List.mem_toFinset.mp hb))
        rcases exists_positive_incoming_arc_at_walkEndpoint
            (tail := tail) (head := head) (y := y) (u := head a) (v := v) (p := p)
            hpTail hpnil hposTail with ⟨b, hb, hbhead, hbpos⟩
        refine ⟨b, ?_, hbhead, hbpos⟩
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem a (List.mem_toFinset.mp hb))

/-- Helper for Theorem 4.11: if a positive walk revisits an earlier vertex after one more positive
arc, the repeated-vertex suffix is already a positive closed walk with nodup internal vertices. -/
private theorem positiveWalkRepeatedVertex_yieldsCircuitSuffix
    {tail head : A → V} {y : A → ℝ}
    {s u : V} {p : List A} {a : A}
    (hp : IsDirectedWalkFromTo tail head s u p)
    (hnodup : (walkVerticesFrom head s p).Nodup)
    (hposp : ∀ b ∈ p.toFinset, 0 < y b)
    (htail : tail a = u)
    (hposa : 0 < y a)
    (hhead : head a ∈ walkVerticesFrom head s p) :
    ∃ c : List A, c ≠ [] ∧ IsDirectedWalkFromTo tail head (head a) (head a) c ∧
      (walkVerticesFrom head (head a) c).tail.Nodup ∧ ∀ b ∈ c.toFinset, 0 < y b := by
  classical
  rcases directedWalk_split_at_visited_vertex hp hhead with
    ⟨p₁, p₂, rfl, hp₁, hp₂⟩
  let w := head a
  let c : List A := p₂ ++ [a]
  have hsingle : IsDirectedWalkFromTo tail head u w [a] := by
    -- The closing arc is a one-step walk back to the repeated vertex.
    exact ⟨htail, rfl⟩
  have hwalkc : IsDirectedWalkFromTo tail head w w c := by
    -- Appending the closing arc turns the suffix into a closed walk.
    simpa [c, w] using directedWalk_append hp₂ hsingle
  have hsplitVertices :
      walkVerticesFrom head s (p₁ ++ p₂) =
        walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail := by
    simpa [w] using walkVerticesFrom_append hp₁ hp₂
  have htailNodup : (walkVerticesFrom head w p₂).tail.Nodup := by
    -- The suffix tail inherits nodup from the original walk after splitting at the repeated
    -- vertex.
    have happendNodup :
        (walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail).Nodup := by
      simpa [hsplitVertices] using hnodup
    exact List.Nodup.of_append_right happendNodup
  have hw_mem_prefix : w ∈ walkVerticesFrom head s p₁ :=
    terminalVertex_mem_walkVerticesFrom hp₁
  have hw_not_mem_suffixTail : w ∉ (walkVerticesFrom head w p₂).tail := by
    have happendNodup :
        (walkVerticesFrom head s p₁ ++ (walkVerticesFrom head w p₂).tail).Nodup := by
      simpa [hsplitVertices] using hnodup
    have hdisj :
        List.Disjoint (walkVerticesFrom head s p₁) ((walkVerticesFrom head w p₂).tail) :=
      List.disjoint_of_nodup_append happendNodup
    exact fun hwTail ↦ (List.disjoint_left.1 hdisj hw_mem_prefix hwTail)
  have hcTailNodup : (walkVerticesFrom head w c).tail.Nodup := by
    have hvertices_c :
        walkVerticesFrom head w c = walkVerticesFrom head w p₂ ++ [w] := by
      -- The closing one-arc walk contributes the repeated basepoint as the final visited vertex.
      have happ := walkVerticesFrom_append hp₂ hsingle
      simpa [c, w, walkVerticesFrom, htail] using happ
    have htail_append :
        (walkVerticesFrom head w c).tail = (walkVerticesFrom head w p₂).tail ++ [w] := by
      cases p₂ with
      | nil =>
          simp [hvertices_c, walkVerticesFrom, c, w]
      | cons b p₂ =>
          simp [hvertices_c, walkVerticesFrom]
    have hdisjTail : List.Disjoint (walkVerticesFrom head w p₂).tail [w] := by
      refine List.disjoint_left.2 ?_
      intro x hx hxw
      simp at hxw
      subst hxw
      exact hw_not_mem_suffixTail hx
    have hnodupTailAppend :
        ((walkVerticesFrom head w p₂).tail ++ [w]).Nodup :=
      List.Nodup.append htailNodup (by simp) hdisjTail
    simpa [htail_append] using hnodupTailAppend
  refine ⟨c, by simp [c], hwalkc, hcTailNodup, ?_⟩
  intro b hb
  have hbList : b ∈ c := List.mem_toFinset.mp hb
  change b ∈ p₂ ++ [a] at hbList
  rcases List.mem_append.mp hbList with hb₂ | hbA
  · exact hposp b (by simpa using List.mem_append.mpr (Or.inr hb₂))
  · have hbEq : b = a := by simpa using hbA
    subst hbEq
    exact hposa

/-- Helper for Theorem 4.11: enlarging the supporting arc set only enlarges the induced undirected
support graph. -/
private theorem supportGraph_mono
    {tail head : A → V} {C D : Finset A} (hCD : C ⊆ D) :
    (arc_induced_digraph tail head C).toSimpleGraphInclusive ≤
      (arc_induced_digraph tail head D).toSimpleGraphInclusive := by
  intro u v huv
  rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj] at huv ⊢
  rcases huv with ⟨hne, huv | huv⟩
  · refine ⟨hne, Or.inl ?_⟩
    rcases (arc_induced_digraph_adj_iff tail head C u v).1 huv with ⟨a, haC, htail, hhead⟩
    exact (arc_induced_digraph_adj_iff tail head D u v).2 ⟨a, hCD haC, htail, hhead⟩
  · refine ⟨hne, Or.inr ?_⟩
    rcases (arc_induced_digraph_adj_iff tail head C v u).1 huv with ⟨a, haC, htail, hhead⟩
    exact (arc_induced_digraph_adj_iff tail head D v u).2 ⟨a, hCD haC, htail, hhead⟩

/-- Helper for Theorem 4.11: the terminal vertex of a directed walk is the last visited vertex. -/
private theorem getLast_walkVerticesFrom
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      let hne : walkVerticesFrom head u p ≠ [] := by
        cases p <;> simp [walkVerticesFrom]
      (walkVerticesFrom head u p).getLast hne = v
  | u, v, [], hwalk => by
      simpa [walkVerticesFrom] using hwalk
  | u, v, a :: p, hwalk => by
      rcases hwalk with ⟨_, hp⟩
      cases p with
      | nil =>
          simpa [walkVerticesFrom] using getLast_walkVerticesFrom hp
      | cons b p =>
          simpa [walkVerticesFrom] using getLast_walkVerticesFrom hp

/-- Helper for Theorem 4.11: the tail sequence of a directed walk is the visited-vertex list with
the terminal vertex removed. -/
private theorem directedWalk_map_tail_eq_dropLast_walkVertices
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      p.map tail = (walkVerticesFrom head u p).dropLast
  | _, _, [], _ => by
      simp [walkVerticesFrom]
  | u, v, a :: p, hwalk => by
      rcases hwalk with ⟨hau, hp⟩
      cases p with
      | nil =>
          simp [walkVerticesFrom, hau]
      | cons b p =>
          simp [walkVerticesFrom, hau, directedWalk_map_tail_eq_dropLast_walkVertices hp]

/-- Helper for Theorem 4.11: every closed directed walk yields an undirected support walk in the
induced support graph with the same visited-vertex set. -/
private theorem exists_supportWalk_of_directedWalk
    {tail head : A → V} :
    ∀ {u v : V} {p : List A}, IsDirectedWalkFromTo tail head u v p →
      ∃ q : ((arc_induced_digraph tail head p.toFinset).toSimpleGraphInclusive).Walk u v,
        ∀ x, x ∈ q.support ↔ x ∈ walkVerticesFrom head u p
  | u, v, [], hwalk => by
      have huv : u = v := by
        simpa [IsDirectedWalkFromTo] using hwalk
      subst v
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      intro x
      simp [walkVerticesFrom]
  | u, v, a :: p, hwalk => by
      rcases hwalk with ⟨hau, hp⟩
      rcases exists_supportWalk_of_directedWalk hp with ⟨q, hq⟩
      have hsubset : p.toFinset ⊆ (a :: p).toFinset := by
        intro b hb
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem a (List.mem_toFinset.mp hb))
      let q' :
          ((arc_induced_digraph tail head (a :: p).toFinset).toSimpleGraphInclusive).Walk
            (head a) v :=
        q.mapLe (supportGraph_mono (tail := tail) (head := head) hsubset)
      have hq' : ∀ x, x ∈ q'.support ↔ x ∈ walkVerticesFrom head (head a) p := by
        intro x
        have hsupport : q'.support = q.support := by
          simpa [q'] using
            (SimpleGraph.Walk.support_mapLe_eq_support
              (p := q)
              (h := supportGraph_mono (tail := tail) (head := head) hsubset))
        rw [hsupport]
        exact hq x
      by_cases hloop : u = head a
      · subst hloop
        refine ⟨q', ?_⟩
        intro x
        have hstart_mem : head a ∈ walkVerticesFrom head (head a) p := by
          cases p with
          | nil =>
              simp [walkVerticesFrom]
          | cons b p =>
              simp [walkVerticesFrom]
        constructor
        · intro hx
          have hx' := (hq' x).1 hx
          exact List.mem_cons_of_mem _ hx'
        · intro hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · exact (hq' _).2 hstart_mem
          · exact (hq' _).2 hx'
      · have hadj :
          ((arc_induced_digraph tail head (a :: p).toFinset).toSimpleGraphInclusive).Adj u
            (head a) := by
          rw [Digraph.toSimpleGraphInclusive, SimpleGraph.fromRel_adj]
          refine ⟨hloop, Or.inl ?_⟩
          exact (arc_induced_digraph_adj_iff tail head (a :: p).toFinset u (head a)).2
            ⟨a, by simp, hau, rfl⟩
        refine ⟨SimpleGraph.Walk.cons hadj q', ?_⟩
        intro x
        constructor
        · intro hx
          rw [SimpleGraph.Walk.support_cons] at hx
          rcases List.mem_cons.mp hx with rfl | hx
          · simp [walkVerticesFrom]
          · exact List.mem_cons_of_mem _ ((hq' x).1 hx)
        · intro hx
          rw [SimpleGraph.Walk.support_cons]
          rcases List.mem_cons.mp hx with rfl | hx
          · simp
          · exact List.mem_cons_of_mem _ ((hq' x).2 hx)

/-- Helper for Theorem 4.11: every visited vertex of a nonempty closed walk is incident to its
support arc set. -/
private theorem mem_circuit_vertex_set_of_mem_walkVertices_closedWalk
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c) {v : V}
    (hv : v ∈ walkVerticesFrom head w c) :
    v ∈ circuit_vertex_set tail head c.toFinset := by
  cases c with
  | nil =>
      exact False.elim (hc_ne rfl)
  | cons a c =>
      rcases hc_walk with ⟨hau, _⟩
      rw [walkVerticesFrom_eq_start_cons_map_head] at hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨a, by simp, Or.inl hau⟩
      · rcases List.mem_map.mp hv with ⟨b, hb, rfl⟩
        exact ⟨b, List.mem_toFinset.mpr hb, Or.inr rfl⟩

/-- Helper for Theorem 4.11: every incident vertex of the support arc set appears on the closed
walk. -/
private theorem mem_walkVertices_of_mem_circuit_vertex_set
    {tail head : A → V} {w : V} {c : List A}
    (hc_walk : IsDirectedWalkFromTo tail head w w c) {v : V}
    (hv : v ∈ circuit_vertex_set tail head c.toFinset) :
    v ∈ walkVerticesFrom head w c := by
  rcases hv with ⟨a, haC, htail | hhead⟩
  · simpa [htail] using
      tail_mem_walkVerticesFrom_of_mem hc_walk (List.mem_toFinset.mp haC)
  · exact List.mem_of_mem_tail <|
      by simpa [hhead] using
        head_mem_walkVerticesTail_of_mem (head := head) (u := w) (p := c)
          (List.mem_toFinset.mp haC)

/-- Helper for Theorem 4.11: the support graph of a nonempty closed directed walk is connected on
its incident vertices. -/
private theorem connectedSupport_of_closedWalk
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c) :
    ((arc_induced_digraph tail head c.toFinset).toSimpleGraphInclusive.induce
      (circuit_vertex_set tail head c.toFinset)).Connected := by
  let G := (arc_induced_digraph tail head c.toFinset).toSimpleGraphInclusive
  rcases exists_supportWalk_of_directedWalk hc_walk with ⟨q, hq⟩
  have hconn : (G.induce {v | v ∈ q.support}).Connected := q.connected_induce_support
  have hverts : {v | v ∈ q.support} = circuit_vertex_set tail head c.toFinset := by
    ext v
    constructor
    · intro hv
      exact mem_circuit_vertex_set_of_mem_walkVertices_closedWalk hc_ne hc_walk ((hq v).1 hv)
    · intro hv
      exact (hq v).2 (mem_walkVertices_of_mem_circuit_vertex_set hc_walk hv)
  rw [hverts] at hconn
  simpa [G] using hconn

/-- Helper for Theorem 4.11: in a nonempty closed walk, the tail-vertex list and head-vertex list
have the same underlying membership. -/
private theorem mem_map_tail_iff_mem_map_head_of_closedWalk
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c) {v : V} :
    v ∈ c.map tail ↔ v ∈ c.map head := by
  let L := walkVerticesFrom head w c
  have hL_ne : L ≠ [] := by
    cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        simp [L, walkVerticesFrom]
  have hL_head : L.head hL_ne = L.getLast hL_ne := by
    have hhead : L.head hL_ne = w := by
      cases c with
      | nil =>
          exact False.elim (hc_ne rfl)
      | cons a c =>
          simp [L, walkVerticesFrom, hL_ne]
    have hlast : L.getLast hL_ne = w := by
      simpa [L] using getLast_walkVerticesFrom hc_walk
    exact hhead.trans hlast.symm
  have hrot : L.dropLast ~r L.tail := List.IsRotated.dropLast_tail hL_ne hL_head
  simpa [L, directedWalk_map_tail_eq_dropLast_walkVertices hc_walk, walkVerticesFrom_tail_eq_map_head]
    using (hrot.mem_iff (a := v))

/-- Helper for Theorem 4.11: the tail-vertex list of a nonempty closed walk is nodup whenever the
head-vertex list is nodup. -/
private theorem map_tail_nodup_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    (c.map tail).Nodup := by
  let L := walkVerticesFrom head w c
  have hL_ne : L ≠ [] := by
    cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        simp [L, walkVerticesFrom]
  have hL_head : L.head hL_ne = L.getLast hL_ne := by
    have hhead : L.head hL_ne = w := by
      cases c with
      | nil =>
          exact False.elim (hc_ne rfl)
      | cons a c =>
          simp [L, walkVerticesFrom, hL_ne]
    have hlast : L.getLast hL_ne = w := by
      simpa [L] using getLast_walkVerticesFrom hc_walk
    exact hhead.trans hlast.symm
  have hrot : L.dropLast ~r L.tail := List.IsRotated.dropLast_tail hL_ne hL_head
  have hdrop : L.dropLast.Nodup := (hrot.nodup_iff).2 hc_nodup
  simpa [L, directedWalk_map_tail_eq_dropLast_walkVertices hc_walk, walkVerticesFrom_tail_eq_map_head]
    using hdrop

/-- Helper for Theorem 4.11: each incident vertex of a nonempty closed walk is the head of exactly
one support arc when the internal visited vertices are pairwise distinct. -/
private theorem incomingArcCount_one_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    ∀ v ∈ circuit_vertex_set tail head c.toFinset, incoming_arc_count head c.toFinset v = 1 := by
  intro v hv
  have hheadNodup : (c.map head).Nodup := by
    simpa [walkVerticesFrom_tail_eq_map_head] using hc_nodup
  have hheadInj := List.inj_on_of_nodup_map hheadNodup
  have hexists : ∃ a, a ∈ c.toFinset ∧ head a = v := by
    rcases hv with ⟨a, haC, htail | hhead⟩
    · have htail_mem : v ∈ c.map tail := by
        rw [← htail]
        exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp haC, rfl⟩
      have hhead_mem : v ∈ c.map head :=
        (mem_map_tail_iff_mem_map_head_of_closedWalk hc_ne hc_walk).1 htail_mem
      rcases List.mem_map.mp hhead_mem with ⟨b, hb, rfl⟩
      exact ⟨b, List.mem_toFinset.mpr hb, rfl⟩
    · exact ⟨a, haC, hhead⟩
  rcases hexists with ⟨a, haC, hheada⟩
  rw [incoming_arc_count, Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext b
  constructor
  · intro hb
    have hbC : b ∈ c.toFinset := (Finset.mem_filter.mp hb).1
    have hbhead : head b = v := (Finset.mem_filter.mp hb).2
    have hEq : b = a :=
      hheadInj (List.mem_toFinset.mp hbC) (List.mem_toFinset.mp haC) (hbhead.trans hheada.symm)
    simp [hEq]
  · intro hb
    have hEq : b = a := by simpa using hb
    subst hEq
    simp [haC, hheada]

/-- Helper for Theorem 4.11: each incident vertex of a nonempty closed walk is the tail of exactly
one support arc when the internal visited vertices are pairwise distinct. -/
private theorem outgoingArcCount_one_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    ∀ v ∈ circuit_vertex_set tail head c.toFinset, outgoing_arc_count tail c.toFinset v = 1 := by
  intro v hv
  have htailNodup : (c.map tail).Nodup :=
    map_tail_nodup_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup
  have htailInj := List.inj_on_of_nodup_map htailNodup
  have hexists : ∃ a, a ∈ c.toFinset ∧ tail a = v := by
    rcases hv with ⟨a, haC, htail | hhead⟩
    · exact ⟨a, haC, htail⟩
    · have hhead_mem : v ∈ c.map head := by
        rw [← hhead]
        exact List.mem_map.mpr ⟨a, List.mem_toFinset.mp haC, rfl⟩
      have htail_mem : v ∈ c.map tail :=
        (mem_map_tail_iff_mem_map_head_of_closedWalk hc_ne hc_walk).2 hhead_mem
      rcases List.mem_map.mp htail_mem with ⟨b, hb, rfl⟩
      exact ⟨b, List.mem_toFinset.mpr hb, rfl⟩
  rcases hexists with ⟨a, haC, htaila⟩
  rw [outgoing_arc_count, Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext b
  constructor
  · intro hb
    have hbC : b ∈ c.toFinset := (Finset.mem_filter.mp hb).1
    have hbtail : tail b = v := (Finset.mem_filter.mp hb).2
    have hEq : b = a :=
      htailInj (List.mem_toFinset.mp hbC) (List.mem_toFinset.mp haC) (hbtail.trans htaila.symm)
    simp [hEq]
  · intro hb
    have hEq : b = a := by simpa using hb
    subst hEq
    simp [haC, htaila]

/-- Helper for Theorem 4.11: a nonempty closed walk with nodup internal visited vertices already
has simple-circuit support. -/
private theorem isSimpleCircuit_of_closedWalk_tailNodup
    {tail head : A → V} {w : V} {c : List A}
    (hc_ne : c ≠ []) (hc_walk : IsDirectedWalkFromTo tail head w w c)
    (hc_nodup : (walkVerticesFrom head w c).tail.Nodup) :
    IsSimpleCircuit tail head c.toFinset := by
  -- Route correction: the missing bridge is exactly the conversion from the extracted closed walk
  -- support to `IsSimpleCircuit`, via connectivity and one-in-one-out counts.
  refine ⟨?_, ?_, ?_⟩
  · cases c with
    | nil =>
        exact False.elim (hc_ne rfl)
    | cons a c =>
        exact ⟨a, by simp⟩
  · -- The undirected support graph is connected because one closed walk already traverses all of
    -- its incident vertices.
    exact connectedSupport_of_closedWalk hc_ne hc_walk
  · intro v hv
    -- The nodup visited-vertex condition upgrades the closed walk support to one-in-one-out.
    exact ⟨incomingArcCount_one_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup v hv,
      outgoingArcCount_one_of_closedWalk_tailNodup hc_ne hc_walk hc_nodup v hv⟩

/-- Helper for Theorem 4.11: a positive sum of nonnegative terms has a positive summand. -/
private theorem exists_pos_of_sum_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ)
    (hnonneg : ∀ i ∈ s, 0 ≤ f i)
    (hsum : 0 < s.sum f) :
    ∃ i ∈ s, 0 < f i := by
  by_contra h
  have hnonpos : ∀ i ∈ s, f i ≤ 0 := by
    intro i hi
    by_contra hpos
    exact h ⟨i, hi, lt_of_not_ge hpos⟩
  have hzero : ∀ i ∈ s, f i = 0 := by
    intro i hi
    linarith [hnonneg i hi, hnonpos i hi]
  have hsum_zero : s.sum f = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    exact hzero i hi
  linarith

/-- Helper for Theorem 4.11: in a circulation, any vertex with a positive incoming arc also has a
positive outgoing arc. -/
private theorem exists_positive_outgoing_arc_of_positive_incoming_circulation
    {tail head : A → V} {z : A → ℝ}
    (hz : IsCirculation tail head z) {v : V}
    (hin : ∃ a, head a = v ∧ 0 < z a) :
    ∃ a, tail a = v ∧ 0 < z a := by
  classical
  have hin_pos : 0 < incoming_flow head z v := by
    rcases hin with ⟨a, ha, hza⟩
    unfold incoming_flow
    have ha_mem : a ∈ Finset.univ.filter (fun e ↦ head e = v) := by
      simp [ha]
    have hle :
        z a ≤ Finset.sum (Finset.univ.filter (fun e ↦ head e = v)) z := by
      exact Finset.single_le_sum (fun b hb ↦ hz.nonneg b) ha_mem
    exact lt_of_lt_of_le hza hle
  have hout_pos : 0 < outgoing_flow tail z v := by
    -- A circulation has equal incoming and outgoing flow at every vertex.
    rw [← hz.flow_conservation v]
    exact hin_pos
  unfold outgoing_flow at hout_pos
  rcases exists_pos_of_sum_pos (Finset.univ.filter fun e ↦ tail e = v) z
      (fun a _ ↦ hz.nonneg a) hout_pos with ⟨a, ha, hza⟩
  exact ⟨a, (Finset.mem_filter.mp ha).2, hza⟩

/-- Helper for Theorem 4.11: every nonzero circulation contains a positive closed walk whose
internal visited vertices are pairwise distinct. -/
private theorem positiveSupportClosedWalk_of_circulation
    {tail head : A → V} {z : A → ℝ}
    (hz : IsCirculation tail head z)
    (hpos : ∃ a, 0 < z a) :
    ∃ w : V, ∃ c : List A, c ≠ [] ∧ IsDirectedWalkFromTo tail head w w c ∧
      (walkVerticesFrom head w c).tail.Nodup ∧ ∀ a ∈ c.toFinset, 0 < z a := by
  classical
  rcases hpos with ⟨a₀, hza₀⟩
  let s := tail a₀
  by_cases hloop : head a₀ = s
  · refine ⟨s, [a₀], by simp, ?_, ?_, ?_⟩
    · simpa [IsDirectedWalkFromTo, s, hloop]
    · simp [walkVerticesFrom, hloop]
    · intro a ha
      have ha' : a = a₀ := by simpa using ha
      simpa [ha'] using hza₀
  · let S : Set (List A) :=
      {p | ∃ u, IsDirectedWalkFromTo tail head s u p ∧
          (walkVerticesFrom head s p).Nodup ∧
          ∀ b ∈ p.toFinset, 0 < z b}
    have hSfinite : S.Finite := by
      refine (List.finite_length_le A (Fintype.card A)).subset ?_
      intro p hpS
      rcases hpS with ⟨u, hwalk, hnodup, _⟩
      have hpNodup : p.Nodup := directedWalk_nodup_of_verticesNodup hwalk hnodup
      exact List.Nodup.length_le_card hpNodup
    have ha₀_in_S : [a₀] ∈ S := by
      refine ⟨head a₀, ?_, ?_, ?_⟩
      · simpa [IsDirectedWalkFromTo, s]
      · simpa [walkVerticesFrom, List.mem_singleton, eq_comm, s] using
          (List.nodup_cons.2
            ⟨by simpa [s, List.mem_singleton, eq_comm] using hloop, List.nodup_singleton _⟩)
      · intro b hb
        have hb' : b = a₀ := by simpa using hb
        simpa [hb'] using hza₀
    have hSnonempty : S.Nonempty := ⟨[a₀], ha₀_in_S⟩
    rcases Set.exists_max_image S List.length hSfinite hSnonempty with ⟨p, hpS, hpmax⟩
    rcases hpS with ⟨u, hwalk, hnodup, hposp⟩
    have hp_nonempty : p ≠ [] := by
      have hmax₀ := hpmax [a₀] ha₀_in_S
      intro hpnil
      simpa [hpnil] using hmax₀
    have hin :
        ∃ a, a ∈ p.toFinset ∧ head a = u ∧ 0 < z a :=
      exists_positive_incoming_arc_at_walkEndpoint hwalk hp_nonempty hposp
    rcases exists_positive_outgoing_arc_of_positive_incoming_circulation hz
        (by
          rcases hin with ⟨a, _, ha, hza⟩
          exact ⟨a, ha, hza⟩) with ⟨a, htail, hza⟩
    by_cases hvisited : head a ∈ walkVerticesFrom head s p
    · rcases positiveWalkRepeatedVertex_yieldsCircuitSuffix hwalk hnodup hposp htail hza hvisited
          with ⟨c, hc_ne, hwalkc, hnodupc, hcpos⟩
      exact ⟨head a, c, hc_ne, hwalkc, hnodupc, hcpos⟩
    · have hsingle : IsDirectedWalkFromTo tail head u (head a) [a] := by
        exact ⟨htail, rfl⟩
      have hwalk' : IsDirectedWalkFromTo tail head s (head a) (p ++ [a]) := by
        exact directedWalk_append hwalk hsingle
      have hvertices' :
          walkVerticesFrom head s (p ++ [a]) = walkVerticesFrom head s p ++ [head a] := by
        have happ := walkVerticesFrom_append hwalk hsingle
        simpa [walkVerticesFrom] using happ
      have hnodup' : (walkVerticesFrom head s (p ++ [a])).Nodup := by
        rw [hvertices']
        refine List.Nodup.append hnodup (by simp) ?_
        refine List.disjoint_left.2 ?_
        intro x hx hxlast
        have hxhead : x = head a := by simpa using hxlast
        subst hxhead
        exact hvisited hx
      have hpos' : ∀ b ∈ (p ++ [a]).toFinset, 0 < z b := by
        intro b hb
        have hb' : b ∈ p ++ [a] := List.mem_toFinset.mp hb
        rcases List.mem_append.mp hb' with hb | hb
        · exact hposp b (by simpa using hb)
        · have hbEq : b = a := by simpa using hb
          subst hbEq
          exact hza
      have hpS' : p ++ [a] ∈ S := by
        exact ⟨head a, hwalk', hnodup', hpos'⟩
      have hle := hpmax (p ++ [a]) hpS'
      exact False.elim (Nat.not_succ_le_self p.length (by simpa using hle))

end

/-- Helper for Theorem 4.11: a nonzero circulation can be peeled by subtracting a positive simple
circuit contribution and thereby strictly shrinking the positive support. -/
theorem decomposeNonzeroCirculationAlongSimpleCircuit
    {V A : Type*} [Fintype A] {tail head : A → V} {x : A → ℝ}
    (hx : x ∈ circulation_cone tail head) (hx_ne : x ≠ 0) :
    ∃ C : Finset A, ∃ μ : ℝ, ∃ y : A → ℝ,
      IsSimpleCircuit tail head C ∧
        0 < μ ∧
        y ∈ circulation_cone tail head ∧
        x = y + μ • circuit_characteristic_vector C ∧
        (Finset.univ.filter (fun a ↦ 0 < y a)).card <
          (Finset.univ.filter (fun a ↦ 0 < x a)).card := by
  classical
  rcases existsSimpleCircuitSubsetPositiveSupport hx hx_ne with ⟨C, hC, hposC⟩
  let values : Finset ℝ := C.image x
  have hvalues_nonempty : values.Nonempty := by
    rcases hC.nonempty with ⟨a, ha⟩
    exact ⟨x a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩
  let μ : ℝ := values.min' hvalues_nonempty
  have hμ_pos : 0 < μ := by
    rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨a, haC, hμ_eq⟩
    have hμ_eq' : μ = x a := by
      simpa [μ] using hμ_eq.symm
    rw [hμ_eq']
    exact hposC a haC
  have hμ_le : ∀ a, a ∈ C → μ ≤ x a := by
    intro a haC
    exact Finset.min'_le values (x a) (Finset.mem_image.mpr ⟨a, haC, rfl⟩)
  let z : A → ℝ := μ • circuit_characteristic_vector C
  let y : A → ℝ := x - z
  have hx_circ : IsCirculation tail head x := (mem_circulation_cone_iff tail head x).1 hx
  have hz_mem : z ∈ circulation_cone tail head := by
    -- The simple-circuit characteristic vector stays in the circulation cone under nonnegative
    -- scaling.
    exact smul_mem_circulationCone (circuitCharacteristicVector_mem_circulationCone hC)
      (le_of_lt hμ_pos)
  have hz_circ : IsCirculation tail head z := (mem_circulation_cone_iff tail head z).1 hz_mem
  have hy_mem : y ∈ circulation_cone tail head := by
    -- Subtracting the minimum circuit value preserves nonnegativity and the balance equations.
    rw [mem_circulation_cone_iff, isCirculation_iff]
    refine ⟨?_, ?_⟩
    · intro v
      calc
        incoming_flow head y v = incoming_flow head x v - incoming_flow head z v := by
          simp [y, incoming_flow, Finset.sum_sub_distrib]
        _ = outgoing_flow tail x v - outgoing_flow tail z v := by
          rw [hx_circ.flow_conservation v, hz_circ.flow_conservation v]
        _ = outgoing_flow tail y v := by
          simp [y, outgoing_flow, Finset.sum_sub_distrib]
    · intro a
      by_cases ha : a ∈ C
      · have hsub_nonneg : 0 ≤ x a - μ := sub_nonneg.mpr (hμ_le a ha)
        simpa [y, z, circuit_characteristic_vector_apply, ha, Pi.smul_apply] using hsub_nonneg
      · simpa [y, z, circuit_characteristic_vector_apply, ha, Pi.smul_apply] using hx_circ.nonneg a
  have hdecomp : x = y + μ • circuit_characteristic_vector C := by
    -- The remainder `y` was defined by subtracting exactly this circuit contribution.
    ext a
    by_cases ha : a ∈ C
    · simp [y, z, circuit_characteristic_vector_apply, ha, Pi.smul_apply]
    · simp [y, z, circuit_characteristic_vector_apply, ha, Pi.smul_apply]
  have hsubset :
      Finset.univ.filter (fun a ↦ 0 < y a) ⊆ Finset.univ.filter (fun a ↦ 0 < x a) := by
    intro a ha
    have hy_pos : 0 < y a := (Finset.mem_filter.mp ha).2
    have hz_nonneg : 0 ≤ z a := hz_circ.nonneg a
    have hx_eval : x a = y a + z a := by
      have hx_eval' := congrArg (fun f : A → ℝ ↦ f a) hdecomp
      simpa using hx_eval'
    have hx_pos : 0 < x a := by
      linarith
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hx_pos⟩
  rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨a₀, ha₀C, hμ_eq⟩
  have ha₀_mem_x :
      a₀ ∈ Finset.univ.filter (fun a ↦ 0 < x a) := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a₀, hposC a₀ ha₀C⟩
  have ha₀_not_mem_y :
      a₀ ∉ Finset.univ.filter (fun a ↦ 0 < y a) := by
    intro ha₀_mem
    have hy_pos : 0 < y a₀ := (Finset.mem_filter.mp ha₀_mem).2
    have hx_eqμ : x a₀ = μ := by
      simpa [μ] using hμ_eq
    have hy_zero : y a₀ = 0 := by
      simp [y, z, circuit_characteristic_vector_apply, ha₀C, Pi.smul_apply, hx_eqμ]
    simpa [hy_zero] using hy_pos
  have hssubset :
      Finset.univ.filter (fun a ↦ 0 < y a) ⊂ Finset.univ.filter (fun a ↦ 0 < x a) := by
    refine (Finset.ssubset_iff_of_subset hsubset).2 ?_
    exact ⟨a₀, ha₀_mem_x, ha₀_not_mem_y⟩
  exact ⟨C, μ, y, hC, hμ_pos, hy_mem, hdecomp, Finset.card_lt_card hssubset⟩

/-- Helper for Theorem 4.11: if every simple circuit evaluates nonnegatively on `d`, then every
circulation does as well. -/
theorem circulationEvaluationNonnegOfSimpleCircuitNonneg
    {V A : Type*} [Fintype A] {tail head : A → V} {d : A → ℝ}
    (hsimple :
      ∀ C : Finset A, IsSimpleCircuit tail head C → 0 ≤ circuit_characteristic_vector C ⬝ᵥ d) :
    ∀ u : A → ℝ, u ∈ circulation_cone tail head → 0 ≤ u ⬝ᵥ d := by
  classical
  let supportCard : (A → ℝ) → ℕ :=
    fun u ↦ (Finset.univ.filter fun a ↦ 0 < u a).card
  have hmain :
      ∀ n : ℕ, ∀ u : A → ℝ, u ∈ circulation_cone tail head →
        supportCard u = n → 0 ≤ u ⬝ᵥ d := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih u hu hcard
    by_cases hu_zero : u = 0
    · simpa [hu_zero]
    · rcases decomposeNonzeroCirculationAlongSimpleCircuit hu hu_zero with
        ⟨C, μ, y, hC, hμ_pos, hy_mem, hdecomp, hy_card_lt⟩
      have hz_nonneg : 0 ≤ (μ • circuit_characteristic_vector C) ⬝ᵥ d := by
        have hC_eval : 0 ≤ circuit_characteristic_vector C ⬝ᵥ d := hsimple C hC
        calc
          0 ≤ μ * (circuit_characteristic_vector C ⬝ᵥ d) := by
            exact mul_nonneg (le_of_lt hμ_pos) hC_eval
          _ = (μ • circuit_characteristic_vector C) ⬝ᵥ d := by
            simp [dotProduct, Pi.smul_apply, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      have hy_nonneg : 0 ≤ y ⬝ᵥ d := by
        exact ih (supportCard y) (by rwa [← hcard]) y hy_mem rfl
      have hu_eval :
          u ⬝ᵥ d = y ⬝ᵥ d + (μ • circuit_characteristic_vector C) ⬝ᵥ d := by
        calc
          u ⬝ᵥ d = (y + μ • circuit_characteristic_vector C) ⬝ᵥ d := by rw [hdecomp]
          _ = y ⬝ᵥ d + (μ • circuit_characteristic_vector C) ⬝ᵥ d := by
              simpa using dotProduct_add y (μ • circuit_characteristic_vector C) d
      linarith
  intro u hu
  exact hmain (supportCard u) u hu rfl

/-- Theorem 4.11. In the loopless complete digraph on `n` vertices, the subtour-elimination
polyhedron is contained in the projection onto the `x`-coordinates of the
Miller-Tucker-Zemlin polyhedron. -/
theorem subtour_polyhedron_subset_proj_x_mtz_polyhedron
    {n : ℕ}
    (root : Fin n) :
    subtour_polyhedron n ⊆ Prod.fst '' mtz_polyhedron root := by
  intro x hx
  rcases (mem_subtour_polyhedron_iff.mp hx) with ⟨hxdeg, _⟩
  -- Route correction: the omitted-root witness setup is already in place, and the local helper
  -- API now closes the Farkas certificate by upgrading the already-proved circuit inequalities to
  -- all circulations through a support-shrinking decomposition.
  rw [mem_imageFst_mtzPolyhedron_iff_existsNonrootPotential]
  refine ⟨hxdeg, ?_⟩
  rw [existsNonrootPotential_iff_augmentedMtzSystem]
  by_contra hno
  obtain ⟨u, hu⟩ :=
    (farkas_lemma_linear_inequalities (augmentedMtzMatrix root) (augmentedMtzRhs root x)).1 hno
  have hu_rhs_nonneg : 0 ≤ u ⬝ᵥ augmentedMtzRhs root x := by
    exact circulationEvaluationNonnegOfSimpleCircuitNonneg
      (d := augmentedMtzRhs root x)
      (fun C hC ↦ simpleCircuit_augmentedMtzRhs_nonneg_of_memSubtour hx hC)
      u (mem_circulationCone_of_annihilatesAugmentedMtzMatrix hu.nonneg hu.annihilates)
  exact (not_lt_of_ge hu_rhs_nonneg) hu.negative_rhs

/-- Source-facing specialization of Theorem 4.11 to the textbook distinguished vertex `1`. -/
theorem subtour_polyhedron_subset_proj_x_textbook_mtz_polyhedron
    {n : ℕ}
    (hpos : 0 < n) :
    subtour_polyhedron n ⊆ Prod.fst '' mtz_polyhedron (textbook_root hpos) :=
  subtour_polyhedron_subset_proj_x_mtz_polyhedron (textbook_root hpos)

end Theorem_4_11

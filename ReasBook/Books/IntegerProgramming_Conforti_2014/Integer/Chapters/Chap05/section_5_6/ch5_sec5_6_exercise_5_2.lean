/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_33
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_4_1.ch5_sec5_4_1_claim_5_4_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9.ch4_sec4_9_lemma_4_45

open scoped BigOperators Matrix

section Exercise52

variable {n p : ℕ}

-- Semantic recall check via `lean_leansearch`: no canonical mathlib owner for a closed facet-count
-- formula for split pairs surfaced, so this file keeps the source-facing Chapter 3/5 split and
-- facet owners.

/-- The mixed-integer coordinates from `(5.1)` are the first `n` coordinates of `ℝ^(n+p)`. -/
def exercise_5_2_integer_indices (n p : ℕ) : Finset (Fin (n + p)) :=
  Finset.univ.image (fun j : Fin n ↦ j.castAdd p)

/-- Helper for Exercise 5.2: `Π₁` and `Π₂` arise from one Chapter 5 split on `P` supported on
the integer coordinates from `(5.1)`. -/
def exercise_5_2_is_split_pair
    (P Pi1 Pi2 : Set (Fin (n + p) → ℝ)) : Prop :=
  ∃ s : Split (exercise_5_2_integer_indices n p),
    Pi1 = split_branch_lower P s s.π0 ∧
      Pi2 = split_branch_upper P s s.π0

/-- Helper for Exercise 5.2: `nFaces k` records the exposed `k`-faces of `Π` in the source
range. -/
def exercise_5_2_has_face_counts
    (Pi : Set (Fin (n + p) → ℝ))
    (nFaces : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ n + p - 2 →
    {F : Set (Fin (n + p) → ℝ) |
        IsExposed ℝ Pi F ∧
          polyhedronDim F = k}.encard =
      (nFaces k : ℕ∞)

/-- Helper for Exercise 5.2: `nFacets` records the number of facets of `Π`. -/
def exercise_5_2_has_facet_count
    (Pi : Set (Fin (n + p) → ℝ))
    (nFacets : ℕ) : Prop :=
  {F : Set (Fin (n + p) → ℝ) | IsFacetOf Pi F}.encard =
    (nFacets : ℕ∞)

/-- Helper for Exercise 5.2: one branch contributes one empty bucket, one zero-dimensional
normalization budget, the source-counted middle-dimensional faces, and one residual top bucket. -/
def exercise_5_2_branchBudget
    (n p : ℕ)
    (nFaces : ℕ → ℕ) : ℕ :=
  1 + (2 * nFaces 1 + 2) +
    Finset.sum (Finset.Icc 1 (n + p - 2)) nFaces +
    (2 * nFaces (n + p - 2) + 3)

/-- Helper for Exercise 5.2: `B` is a combinatorial facet bound if, in the source regime
`3 ≤ n + p`, it bounds the number of facets of `conv(Π₁ ∪ Π₂)` using only the source face-count
functions of the two split branches. -/
def exercise_5_2_is_combinatorial_facet_bound
    (n p : ℕ)
    (B : (ℕ → ℕ) → (ℕ → ℕ) → ℕ) : Prop :=
  ∀ (P Pi1 Pi2 : Set (Fin (n + p) → ℝ))
    (nFaces1 nFaces2 : ℕ → ℕ),
      is_polyhedron P →
      exercise_5_2_is_split_pair P Pi1 Pi2 →
      3 ≤ n + p →
      exercise_5_2_has_face_counts Pi1 nFaces1 →
      exercise_5_2_has_face_counts Pi2 nFaces2 →
      {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F}.encard ≤
        (B nFaces1 nFaces2 : ℕ∞)

/-- Helper for Exercise 5.2: every member `P m` of the family has an `m`-constraint matrix
presentation. -/
def exercise_5_2_has_m_constraint_presentations
    (d : ℕ → ℕ)
    (P : ∀ m : ℕ, Set (Fin (d m) → ℝ)) : Prop :=
  ∀ m : ℕ, ∃ A : Matrix (Fin m) (Fin (d m)) ℝ, ∃ b : Fin m → ℝ,
    P m = polyhedron_le_set A b

/-- Helper for Exercise 5.2: each pair `Π₁ m`, `Π₂ m` is obtained from the same Chapter 5 split
on `P m` supported on the designated mixed-integer coordinates `I m`. -/
def exercise_5_2_is_split_family
    (d : ℕ → ℕ)
    (I : ∀ m : ℕ, Finset (Fin (d m)))
    (P Pi1 Pi2 : ∀ m : ℕ, Set (Fin (d m) → ℝ)) : Prop :=
  ∀ m : ℕ, ∃ s : Split (I m),
    Pi1 m = split_branch_lower (P m) s s.π0 ∧
      Pi2 m = split_branch_upper (P m) s s.π0

/-- Helper for Exercise 5.2: the split-disjunctive hull family eventually beats every linear
facet bound. -/
def exercise_5_2_has_superlinear_split_disjunctive_facet_growth
    (d : ℕ → ℕ)
    (Pi1 Pi2 : ∀ m : ℕ, Set (Fin (d m) → ℝ)) : Prop :=
  ∀ C : ℕ, ∃ m : ℕ,
    (C * m : ℕ∞) <
      {F : Set (Fin (d m) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 m ∪ Pi2 m)) F}.encard

/-- Helper for Exercise 5.2: a split pair rewrites `convexHull ℝ (Π₁ ∪ Π₂)` to the canonical
Chapter 5 split-hull owner attached to the same split data. -/
lemma splitPair_convexHull_eq_splitHull
    {P Pi1 Pi2 : Set (Fin (n + p) → ℝ)}
    (hsplit : exercise_5_2_is_split_pair (n := n) (p := p) P Pi1 Pi2) :
    ∃ s : Split (exercise_5_2_integer_indices n p),
      convexHull ℝ (Pi1 ∪ Pi2) = split_hull P s s.π0 := by
  rcases hsplit with ⟨s, rfl, rfl⟩
  -- Normalize the target hull to the canonical split-hull owner before counting faces.
  refine ⟨s, ?_⟩
  simp [split_hull]

/-- Helper for Exercise 5.2: the hull of a split pair is polyhedral because it is a Chapter 5
split hull of the ambient polyhedron. -/
lemma splitPair_convexHull_isPolyhedron
    {P Pi1 Pi2 : Set (Fin (n + p) → ℝ)}
    (hP : is_polyhedron P)
    (hsplit : exercise_5_2_is_split_pair (n := n) (p := p) P Pi1 Pi2) :
    is_polyhedron (convexHull ℝ (Pi1 ∪ Pi2)) := by
  rcases hP with ⟨m, A, b, rfl⟩
  rcases hsplit with ⟨s, rfl, rfl⟩
  -- Normalize both branches to the canonical two-row split presentation.
  simpa [split_branch_lower, split_branch_upper, split_dot] using
    convexHull_split_polyhedra_is_polyhedron
      A b (fun j ↦ (s.1 j : ℝ)) (s.π0 : ℝ) ((s.π0 : ℝ) + 1)

/-- Helper for Exercise 5.2: a split-pair hull has only finitely many facets. -/
lemma splitPair_finiteFacets
    {P Pi1 Pi2 : Set (Fin (n + p) → ℝ)}
    (hP : is_polyhedron P)
    (hsplit : exercise_5_2_is_split_pair (n := n) (p := p) P Pi1 Pi2) :
    Set.Finite {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F} := by
  have hHull_polyhedron :
      is_polyhedron (convexHull ℝ (Pi1 ∪ Pi2)) :=
    splitPair_convexHull_isPolyhedron (n := n) (p := p) hP hsplit
  -- Facets form a subfamily of the finite exposed-face family of the hull polyhedron.
  refine (polyhedron_finite_faces (P := convexHull ℝ (Pi1 ∪ Pi2)) hHull_polyhedron).subset ?_
  intro F hF
  exact (isFacetOf_iff.mp hF).2.1

/-- Helper for Exercise 5.2: each counted family of exposed branch faces is finite because the
face-count hypothesis identifies its cardinality with a natural number. -/
lemma countedFaceFamily_finite
    {Pi : Set (Fin (n + p) → ℝ)}
    {nFaces : ℕ → ℕ}
    (hFaces : exercise_5_2_has_face_counts (n := n) (p := p) Pi nFaces)
    {k : ℕ}
    (hk1 : 1 ≤ k)
    (hk2 : k ≤ n + p - 2) :
    Set.Finite {F : Set (Fin (n + p) → ℝ) |
      IsExposed ℝ Pi F ∧ polyhedronDim F = k} := by
  -- The source face-count equality already realizes this family as a finite cardinal.
  exact Set.finite_of_encard_eq_coe (hFaces k hk1 hk2)

/-- Helper for Exercise 5.2: summing the prescribed dimension-by-dimension counts bounds the
whole middle-dimensional exposed-face family. -/
lemma middleFaceFamily_encard_le_sum
    {Pi : Set (Fin (n + p) → ℝ)}
    {nFaces : ℕ → ℕ}
    (hFaces : exercise_5_2_has_face_counts (n := n) (p := p) Pi nFaces) :
    {F : Set (Fin (n + p) → ℝ) |
        IsExposed ℝ Pi F ∧
          1 ≤ polyhedronDim F ∧ polyhedronDim F ≤ n + p - 2}.encard ≤
      (Finset.sum (Finset.Icc 1 (n + p - 2)) nFaces : ℕ) := by
  let exactFaces : ℕ → Set (Set (Fin (n + p) → ℝ)) := fun k ↦
    {F | IsExposed ℝ Pi F ∧ polyhedronDim F = k}
  have hsubset :
      {F : Set (Fin (n + p) → ℝ) |
          IsExposed ℝ Pi F ∧
            1 ≤ polyhedronDim F ∧ polyhedronDim F ≤ n + p - 2} ⊆
        ⋃ k ∈ Finset.Icc 1 (n + p - 2), exactFaces k := by
    intro F hF
    simp only [Finset.mem_Icc, Set.mem_iUnion]
    exact ⟨polyhedronDim F, ⟨hF.2.1, hF.2.2⟩, hF.1, rfl⟩
  calc
    {F : Set (Fin (n + p) → ℝ) |
        IsExposed ℝ Pi F ∧
          1 ≤ polyhedronDim F ∧ polyhedronDim F ≤ n + p - 2}.encard ≤
        (⋃ k ∈ Finset.Icc 1 (n + p - 2), exactFaces k).encard :=
      Set.encard_mono hsubset
    _ ≤ ∑ k ∈ Finset.Icc 1 (n + p - 2), (exactFaces k).encard :=
      Finset.set_encard_biUnion_le _ _
    _ = (Finset.sum (Finset.Icc 1 (n + p - 2)) nFaces : ℕ) := by
      calc
        ∑ k ∈ Finset.Icc 1 (n + p - 2), (exactFaces k).encard =
            ∑ k ∈ Finset.Icc 1 (n + p - 2), (nFaces k : ℕ∞) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hkBounds : 1 ≤ k ∧ k ≤ n + p - 2 := Finset.mem_Icc.mp hk
              simpa [exactFaces] using hFaces k hkBounds.1 hkBounds.2
        _ = (Finset.sum (Finset.Icc 1 (n + p - 2)) nFaces : ℕ) := by
              norm_cast

/-- Helper for Exercise 5.2: the zero-dimensional exposed-face bucket, including the conventional
empty face whose affine-span direction also has rank zero. -/
private def branchZeroFaces (Pi : Set (Fin (n + p) → ℝ)) :
    Set (Set (Fin (n + p) → ℝ)) :=
  {F | IsExposed ℝ Pi F ∧ polyhedronDim F = 0}

/-- Helper for Exercise 5.2: the exposed faces in the source-counted middle dimensions. -/
private def branchMiddleFaces (Pi : Set (Fin (n + p) → ℝ)) :
    Set (Set (Fin (n + p) → ℝ)) :=
  {F | IsExposed ℝ Pi F ∧
    1 ≤ polyhedronDim F ∧ polyhedronDim F ≤ n + p - 2}

/-- Helper for Exercise 5.2: the residual exposed faces in the two possible ambient top ranks. -/
private def branchTopFaces (Pi : Set (Fin (n + p) → ℝ)) :
    Set (Set (Fin (n + p) → ℝ)) :=
  {F | IsExposed ℝ Pi F ∧ n + p - 1 ≤ polyhedronDim F}

/-- Helper for Exercise 5.2: all exposed faces after auditing their dimension bucket. -/
private def branchAuditedFaces (Pi : Set (Fin (n + p) → ℝ)) :
    Set (Set (Fin (n + p) → ℝ)) :=
  {F | IsExposed ℝ Pi F ∧
    (F = ∅ ∨ polyhedronDim F = 0 ∨
      (1 ≤ polyhedronDim F ∧ polyhedronDim F ≤ n + p - 2) ∨
      n + p - 1 ≤ polyhedronDim F)}

/-- Helper for Exercise 5.2: once the two boundary buckets are controlled, the prescribed middle
counts give the complete branch budget. -/
private lemma branchAuditedFaces_encard_le_branchBudget
    {Pi : Set (Fin (n + p) → ℝ)}
    {nFaces : ℕ → ℕ}
    (hFaces : exercise_5_2_has_face_counts (n := n) (p := p) Pi nFaces)
    (hzero : (branchZeroFaces (n := n) (p := p) Pi).encard ≤
      ((2 * nFaces 1 + 2 : ℕ) : ℕ∞))
    (htop : (branchTopFaces (n := n) (p := p) Pi).encard ≤
      ((2 * nFaces (n + p - 2) + 3 : ℕ) : ℕ∞)) :
    (branchAuditedFaces (n := n) (p := p) Pi).encard ≤
      (exercise_5_2_branchBudget n p nFaces : ℕ∞) := by
  let emptyFamily : Set (Set (Fin (n + p) → ℝ)) := {∅}
  have hsubset :
      branchAuditedFaces (n := n) (p := p) Pi ⊆
        ((emptyFamily ∪ branchZeroFaces (n := n) (p := p) Pi) ∪
          branchMiddleFaces (n := n) (p := p) Pi) ∪
            branchTopFaces (n := n) (p := p) Pi := by
    intro F hF
    rcases hF.2 with hEmpty | hZero | hMiddle | hTop
    · exact Or.inl (Or.inl (Or.inl (by simp [emptyFamily, hEmpty])))
    · exact Or.inl (Or.inl (Or.inr ⟨hF.1, hZero⟩))
    · exact Or.inl (Or.inr ⟨hF.1, hMiddle⟩)
    · exact Or.inr ⟨hF.1, hTop⟩
  have hmiddle :
      (branchMiddleFaces (n := n) (p := p) Pi).encard ≤
        (Finset.sum (Finset.Icc 1 (n + p - 2)) nFaces : ℕ) := by
    simpa [branchMiddleFaces] using
      middleFaceFamily_encard_le_sum (n := n) (p := p) hFaces
  calc
    (branchAuditedFaces (n := n) (p := p) Pi).encard ≤
        (((emptyFamily ∪ branchZeroFaces (n := n) (p := p) Pi) ∪
          branchMiddleFaces (n := n) (p := p) Pi) ∪
            branchTopFaces (n := n) (p := p) Pi).encard := Set.encard_mono hsubset
    _ ≤ ((emptyFamily ∪ branchZeroFaces (n := n) (p := p) Pi) ∪
          branchMiddleFaces (n := n) (p := p) Pi).encard +
        (branchTopFaces (n := n) (p := p) Pi).encard := Set.encard_union_le _ _
    _ ≤ (emptyFamily ∪ branchZeroFaces (n := n) (p := p) Pi).encard +
          (branchMiddleFaces (n := n) (p := p) Pi).encard +
        (branchTopFaces (n := n) (p := p) Pi).encard := by
          gcongr
          exact Set.encard_union_le _ _
    _ ≤ (emptyFamily.encard + (branchZeroFaces (n := n) (p := p) Pi).encard) +
          (branchMiddleFaces (n := n) (p := p) Pi).encard +
        (branchTopFaces (n := n) (p := p) Pi).encard := by
          gcongr
          exact Set.encard_union_le _ _
    _ ≤ (1 : ℕ∞) + (2 * nFaces 1 + 2 : ℕ) +
          (Finset.sum (Finset.Icc 1 (n + p - 2)) nFaces : ℕ) +
        (2 * nFaces (n + p - 2) + 3 : ℕ) := by
          simp only [emptyFamily, Set.encard_singleton]
          gcongr
    _ = (exercise_5_2_branchBudget n p nFaces : ℕ∞) := by
          simp [exercise_5_2_branchBudget]

/-- Helper for Exercise 5.2: in a space of dimension at most two, three linear functionals
cannot each have a point where it alone vanishes while the other two are strictly negative. -/
private lemma three_functionals_not_pairwise_exclusive
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V ≤ 2)
    (a b c : Module.Dual ℝ V)
    (u v w : V)
    (hau : a u = 0) (hbu : b u < 0) (hcu : c u < 0)
    (hav : a v < 0) (hbv : b v = 0) (hcv : c v < 0)
    (haw : a w < 0) (hbw : b w < 0) (hcw : c w = 0) : False := by
  have ha_ne : a ≠ 0 := by
    intro ha
    have := congrArg (fun f : Module.Dual ℝ V ↦ f v) ha
    simp [hav.ne] at this
  have hab : LinearIndependent ℝ ![a, b] := by
    rw [LinearIndependent.pair_iff' ha_ne]
    intro t htab
    have heval := congrArg (fun f : Module.Dual ℝ V ↦ f u) htab
    simp [hau] at heval
    linarith
  have hdim_ge : 2 ≤ Module.finrank ℝ V := by
    have hspan := Submodule.finrank_mono
      (show Submodule.span ℝ (Set.range ![a, b]) ≤
        (⊤ : Submodule ℝ (Module.Dual ℝ V)) from le_top)
    rw [finrank_span_eq_card hab] at hspan
    simpa using hspan
  have hdim_eq : Module.finrank ℝ V = 2 := by omega
  have hspan_top : Submodule.span ℝ (Set.range ![a, b]) = ⊤ :=
    hab.span_eq_top_of_card_eq_finrank (by simp [hdim_eq])
  have hc_span : c ∈ Submodule.span ℝ ({a, b} : Set (Module.Dual ℝ V)) := by
    have hc_top : c ∈ (⊤ : Submodule ℝ (Module.Dual ℝ V)) := trivial
    rw [← hspan_top] at hc_top
    have hc_ba : c ∈ Submodule.span ℝ ({b, a} : Set (Module.Dual ℝ V)) := by
      simpa using hc_top
    have hp : ({b, a} : Set (Module.Dual ℝ V)) = {a, b} := by
      ext f
      simp [or_comm]
    rwa [hp] at hc_ba
  rcases Submodule.mem_span_pair.mp hc_span with ⟨α, β, habc⟩
  have hu_eval := congrArg (fun f : Module.Dual ℝ V ↦ f u) habc
  have hv_eval := congrArg (fun f : Module.Dual ℝ V ↦ f v) habc
  have hw_eval := congrArg (fun f : Module.Dual ℝ V ↦ f w) habc
  have hβ_pos : 0 < β := by
    by_contra hβ
    have hβ_nonpos : β ≤ 0 := le_of_not_gt hβ
    have hmul : 0 ≤ β * b u := mul_nonneg_of_nonpos_of_nonpos hβ_nonpos hbu.le
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hau, mul_zero,
      zero_add] at hu_eval
    linarith
  have hα_pos : 0 < α := by
    by_contra hα
    have hα_nonpos : α ≤ 0 := le_of_not_gt hα
    have hmul : 0 ≤ α * a v := mul_nonneg_of_nonpos_of_nonpos hα_nonpos hav.le
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hbv, mul_zero,
      add_zero] at hv_eval
    linarith
  have hαw : α * a w < 0 := mul_neg_of_pos_of_neg hα_pos haw
  have hβw : β * b w < 0 := mul_neg_of_pos_of_neg hβ_pos hbw
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hw_eval
  linarith

/-- Helper for Exercise 5.2: a dual of a vector space of dimension at most one again has
dimension at most one. -/
private lemma dual_finrank_le_one_of_finrank_le_one
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V ≤ 1) :
    Module.finrank ℝ (Module.Dual ℝ V) ≤ 1 := by
  -- Rewrite the dual dimension in a fresh declaration before entering the large facet proof.
  calc
    Module.finrank ℝ (Module.Dual ℝ V) = Module.finrank ℝ V :=
      Subspace.dual_finrank_eq
    _ ≤ 1 := hdim

/-- Helper for Exercise 5.2: on a vector space of dimension at most one, three affine
inequalities cannot each have a point where exactly that inequality is tight. -/
private lemma three_affine_functionals_not_pairwise_exclusive
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V ≤ 1)
    (a b c : Module.Dual ℝ V) (ra rb rc : ℝ)
    (u v w : V) (huv : u ≠ v)
    (hau : a u = ra) (hbu : b u < rb) (hcu : c u < rc)
    (hav : a v < ra) (hbv : b v = rb) (hcv : c v < rc)
    (haw : a w < ra) (hbw : b w < rb) (hcw : c w = rc) : False := by
  let uv : V := v - u
  have huv_ne : uv ≠ 0 := by simpa [uv, sub_ne_zero] using huv.symm
  have hdim_pos : 0 < Module.finrank ℝ V :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨uv, huv_ne⟩
  have hdim_eq : Module.finrank ℝ V = 1 := by omega
  obtain ⟨t, ht⟩ :=
    ((finrank_eq_one_iff_of_nonzero' uv huv_ne).mp hdim_eq) (w - u)
  have hw_line : w = AffineMap.lineMap u v t := by
    rw [AffineMap.lineMap_apply_module']
    have ht' : t • (v - u) = w - u := by simpa [uv] using ht
    rw [ht']
    abel
  have ha_eval := congrArg a hw_line
  have hb_eval := congrArg b hw_line
  have hc_eval := congrArg c hw_line
  simp only [AffineMap.lineMap_apply_module, map_add, map_smul,
    smul_eq_mul] at ha_eval hb_eval hc_eval
  have ht_pos : 0 < t := by
    by_contra ht
    have ht_nonpos : t ≤ 0 := le_of_not_gt ht
    nlinarith
  have ht_lt_one : t < 1 := by
    by_contra ht
    have ht_ge : 1 ≤ t := le_of_not_gt ht
    nlinarith
  nlinarith

/-- Helper for Exercise 5.2: an affine set of direction dimension at most one cannot contain
three distinct extreme points.  A nonzero difference spans the direction, so the third point is
either inside the first segment or beyond one of its endpoints. -/
private lemma three_extremePoints_impossible_of_finrank_affineSpan_le_one
    {d : ℕ} {Q : Set (Fin d → ℝ)} {x y z : Fin d → ℝ}
    (hdim : Module.finrank ℝ (affineSpan ℝ Q).direction ≤ 1)
    (hx : x ∈ Q.extremePoints ℝ)
    (hy : y ∈ Q.extremePoints ℝ)
    (hz : z ∈ Q.extremePoints ℝ)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : False := by
  let D : Submodule ℝ (Fin d → ℝ) := (affineSpan ℝ Q).direction
  let vxy : D := ⟨y - x, by
    simpa [D, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ Q hy.1) (subset_affineSpan ℝ Q hx.1)⟩
  let vxz : D := ⟨z - x, by
    simpa [D, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ Q hz.1) (subset_affineSpan ℝ Q hx.1)⟩
  have hvxy_ne : vxy ≠ 0 := by
    intro hv
    have hv' := congrArg (fun v : D ↦ (v : Fin d → ℝ)) hv
    have hv'' : y - x = 0 := by simpa [vxy] using hv'
    exact hxy (sub_eq_zero.mp hv'').symm
  have hdim_pos : 0 < Module.finrank ℝ D :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨vxy, hvxy_ne⟩
  have hdim_eq : Module.finrank ℝ D = 1 := by
    dsimp [D] at hdim_pos ⊢
    omega
  obtain ⟨a, ha⟩ :=
    ((finrank_eq_one_iff_of_nonzero' vxy hvxy_ne).mp hdim_eq) vxz
  have ha_ambient : a • (y - x) = z - x := by
    simpa [vxy, vxz] using congrArg (fun v : D ↦ (v : Fin d → ℝ)) ha
  have hz_line : z = AffineMap.lineMap x y a := by
    rw [AffineMap.lineMap_apply_module']
    rw [ha_ambient]
    abel
  by_cases ha_open : a ∈ Set.Ioo (0 : ℝ) 1
  · have hz_open : z ∈ openSegment ℝ x y := by
      rw [openSegment_eq_image_lineMap]
      exact ⟨a, ha_open, hz_line.symm⟩
    have hx_eq_z := (mem_extremePoints_iff_left.mp hz).2 x hx.1 y hy.1 hz_open
    exact hxz hx_eq_z
  · have ha_zero : a ≠ 0 := by
      intro ha0
      apply hxz
      simpa [ha0] using hz_line.symm
    have ha_one : a ≠ 1 := by
      intro ha1
      apply hyz
      simpa [ha1] using hz_line.symm
    have ha_outside : a < 0 ∨ 1 < a := by
      rcases lt_trichotomy a 0 with haNeg | haZero | haPos
      · exact Or.inl haNeg
      · exact False.elim (ha_zero haZero)
      · rcases lt_trichotomy a 1 with haLt | haEq | haGt
        · exact False.elim (ha_open ⟨haPos, haLt⟩)
        · exact False.elim (ha_one haEq)
        · exact Or.inr haGt
    exact extreme_endpoints_forbid_outside_collinear_point
      hx hy hxy hz.1 hz_line ha_outside

/-- Helper for Exercise 5.2: a one-dimensional exposed face has at most two nonempty
zero-dimensional exposed subfaces.  Such a subface is a singleton extreme point of the containing
face, and three distinct endpoints are impossible on an affine line. -/
private lemma oneDimensionalExposedFace_zeroSubfaces_encard_le_two
    {d : ℕ} {Q G : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q)
    (hG_exposed : IsExposed ℝ Q G)
    (hG_dim : polyhedronDim G = 1) :
    {F : Set (Fin d → ℝ) |
      IsExposed ℝ Q F ∧ F.Nonempty ∧ F ⊆ G ∧ polyhedronDim F = 0}.encard ≤
        (2 : ℕ∞) := by
  classical
  let endpoints : Set (Set (Fin d → ℝ)) :=
    {F | IsExposed ℝ Q F ∧ F.Nonempty ∧ F ⊆ G ∧ polyhedronDim F = 0}
  have hendpoints_finite : endpoints.Finite :=
    (polyhedron_finite_faces hQ).subset (fun _ hF ↦ hF.1)
  change endpoints.encard ≤ (2 : ℕ∞)
  refine (Set.encard_le_coe_iff_finite_ncard_le (s := endpoints) (k := 2)).2
    ⟨hendpoints_finite, ?_⟩
  by_contra hle
  have hthree : 2 < endpoints.ncard := lt_of_not_ge hle
  obtain ⟨F₁, hF₁, F₂, hF₂, F₃, hF₃, hF₁F₂, hF₁F₃, hF₂F₃⟩ :=
    (Set.two_lt_ncard (s := endpoints) hendpoints_finite).mp hthree
  obtain ⟨x₁, hx₁F₁⟩ := hF₁.2.1
  obtain ⟨x₂, hx₂F₂⟩ := hF₂.2.1
  obtain ⟨x₃, hx₃F₃⟩ := hF₃.2.1
  obtain ⟨y₁, hF₁_singleton⟩ :=
    exists_eq_singleton_of_nonempty_finrank_direction_affineSpan_eq_zero
      hF₁.2.1 (by simpa [polyhedronDim] using hF₁.2.2.2)
  obtain ⟨y₂, hF₂_singleton⟩ :=
    exists_eq_singleton_of_nonempty_finrank_direction_affineSpan_eq_zero
      hF₂.2.1 (by simpa [polyhedronDim] using hF₂.2.2.2)
  obtain ⟨y₃, hF₃_singleton⟩ :=
    exists_eq_singleton_of_nonempty_finrank_direction_affineSpan_eq_zero
      hF₃.2.1 (by simpa [polyhedronDim] using hF₃.2.2.2)
  have hx₁y₁ : x₁ = y₁ := by simpa [hF₁_singleton] using hx₁F₁
  have hx₂y₂ : x₂ = y₂ := by simpa [hF₂_singleton] using hx₂F₂
  have hx₃y₃ : x₃ = y₃ := by simpa [hF₃_singleton] using hx₃F₃
  subst y₁
  subst y₂
  subst y₃
  have hlocal₁ : IsExposed ℝ G F₁ :=
    (isExposed_iff_isExposed_of_subset hQ hG_exposed).2 ⟨hF₁.1, hF₁.2.2.1⟩
  have hlocal₂ : IsExposed ℝ G F₂ :=
    (isExposed_iff_isExposed_of_subset hQ hG_exposed).2 ⟨hF₂.1, hF₂.2.2.1⟩
  have hlocal₃ : IsExposed ℝ G F₃ :=
    (isExposed_iff_isExposed_of_subset hQ hG_exposed).2 ⟨hF₃.1, hF₃.2.2.1⟩
  have hx₁extreme : x₁ ∈ G.extremePoints ℝ := by
    rw [hF₁_singleton] at hlocal₁
    exact hlocal₁.isExtreme.mem_extremePoints
  have hx₂extreme : x₂ ∈ G.extremePoints ℝ := by
    rw [hF₂_singleton] at hlocal₂
    exact hlocal₂.isExtreme.mem_extremePoints
  have hx₃extreme : x₃ ∈ G.extremePoints ℝ := by
    rw [hF₃_singleton] at hlocal₃
    exact hlocal₃.isExtreme.mem_extremePoints
  have hx₁x₂ : x₁ ≠ x₂ := by
    intro h
    apply hF₁F₂
    simp [hF₁_singleton, hF₂_singleton, h]
  have hx₁x₃ : x₁ ≠ x₃ := by
    intro h
    apply hF₁F₃
    simp [hF₁_singleton, hF₃_singleton, h]
  have hx₂x₃ : x₂ ≠ x₃ := by
    intro h
    apply hF₂F₃
    simp [hF₂_singleton, hF₃_singleton, h]
  exact three_extremePoints_impossible_of_finrank_affineSpan_le_one
    (by simpa [polyhedronDim] using hG_dim.le) hx₁extreme hx₂extreme hx₃extreme
      hx₁x₂ hx₁x₃ hx₂x₃

/-- Helper for Exercise 5.2: every nonempty exposed face of a polyhedron is itself a polyhedron.
This is the presentation bridge used when a face becomes the ambient set in a local incidence
argument. -/
private lemma isPolyhedron_of_nonempty_isExposed
    {d : ℕ} {Q G : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q) (hG_nonempty : G.Nonempty) (hG : IsExposed ℝ Q G) :
    is_polyhedron G := by
  rcases hQ with ⟨m, A, b, rfl⟩
  obtain ⟨I, hI⟩ :=
    exists_eq_active_constraint_face_of_isExposed A b G hG hG_nonempty
  rw [hI, active_constraint_face_eq_polyhedronAux]
  exact ⟨m + m, activeConstraintFaceMatrix A I, activeConstraintFaceRhs b I, rfl⟩

/-- Helper for Exercise 5.2: every nonempty zero-dimensional face of a positive-dimensional
polyhedron lies in a one-dimensional exposed face.  Choose a minimal strict exposed superface;
minimality makes the original face a facet of it, hence forces a one-step rank increase. -/
private lemma exists_oneDimensional_exposed_superface
    {d : ℕ} {Q F : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q)
    (hF_nonempty : F.Nonempty)
    (hF_exposed : IsExposed ℝ Q F)
    (hF_dim : polyhedronDim F = 0)
    (hQ_dim : 1 ≤ polyhedronDim Q) :
    ∃ G : Set (Fin d → ℝ),
      IsExposed ℝ Q G ∧ F ⊆ G ∧ polyhedronDim G = 1 := by
  classical
  let candidates : Set (Set (Fin d → ℝ)) :=
    {G | IsExposed ℝ Q G ∧ F ⊂ G}
  have hF_ne_Q : F ≠ Q := by
    intro h
    rw [h] at hF_dim
    omega
  have hQ_candidate : Q ∈ candidates :=
    ⟨IsExposed.refl Q, hF_exposed.subset.ssubset_of_ne hF_ne_Q⟩
  have hcandidates_finite : candidates.Finite :=
    (polyhedron_finite_faces hQ).subset (fun _ hG ↦ hG.1)
  obtain ⟨G, _hGQ, hG_minimal⟩ :=
    hcandidates_finite.exists_le_minimal hQ_candidate
  have hG_exposed : IsExposed ℝ Q G := hG_minimal.prop.1
  have hFG : F ⊂ G := hG_minimal.prop.2
  have hF_local : IsExposed ℝ G F :=
    (isExposed_iff_isExposed_of_subset hQ hG_exposed).2 ⟨hF_exposed, hFG.subset⟩
  have hF_proper_local : is_proper_face G F :=
    (is_proper_face_iff).2 ⟨hF_local, hF_nonempty, hFG⟩
  have hF_facet_local : is_facet G F := by
    rw [is_facet_iff]
    refine ⟨hF_proper_local, ?_⟩
    intro H hH_proper hFH
    by_contra hHF
    have hFH_strict : F ⊂ H := hFH.ssubset_of_ne (Ne.symm hHF)
    have hH_local : IsExposed ℝ G H := (is_proper_face_iff.mp hH_proper).1
    have hH_ambient : IsExposed ℝ Q H ∧ H ⊆ G :=
      (isExposed_iff_isExposed_of_subset hQ hG_exposed).1 hH_local
    have hH_candidate : H ∈ candidates := ⟨hH_ambient.1, hFH_strict⟩
    have hHG : H = G := Minimal.eq_of_subset hG_minimal hH_candidate hH_ambient.2
    exact (is_proper_face_iff.mp hH_proper).2.2.ne hHG
  have hG_polyhedron : is_polyhedron G :=
    isPolyhedron_of_nonempty_isExposed hQ (hF_nonempty.mono hFG.subset) hG_exposed
  rcases hG_polyhedron with ⟨m, A, b, hG_eq⟩
  have hG_nonempty : G.Nonempty := hF_nonempty.mono hFG.subset
  have hF_local' : IsExposed ℝ (polyhedron_le_set A b) F := by
    rw [← hG_eq]
    exact hF_local
  have hF_facet_local' : is_facet (polyhedron_le_set A b) F := by
    rw [← hG_eq]
    exact hF_facet_local
  have hstep :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A b (by simpa [← hG_eq] using hG_nonempty) F hF_local').mp hF_facet_local'
  refine ⟨G, hG_exposed, hFG.subset, ?_⟩
  rw [polyhedronDim]
  have hdimF : Module.finrank ℝ (affineSpan ℝ F).direction = 0 := by
    simpa [polyhedronDim] using hF_dim
  have hstep' :
      Module.finrank ℝ (affineSpan ℝ F).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ G).direction := by
    rw [hG_eq]
    exact hstep.2
  omega

/-- Helper for Exercise 5.2: count a left family by a finite right family when every left object
is incident to a right object and every right incidence fiber has a uniform bound. -/
private lemma finiteIncidenceEncard_le
    {X Y : Type*} {L : Set X} {R : Set Y} {Inc : X → Y → Prop} {c : ℕ∞}
    (hR : R.Finite)
    (hcover : ∀ x ∈ L, ∃ y ∈ R, Inc x y)
    (hfiber : ∀ y ∈ R, {x : X | x ∈ L ∧ Inc x y}.encard ≤ c) :
    L.encard ≤ c * R.encard := by
  classical
  let fiber : Y → Set X := fun y ↦ {x | x ∈ L ∧ Inc x y}
  have hsubset : L ⊆ ⋃ y ∈ hR.toFinset, fiber y := by
    intro x hx
    obtain ⟨y, hyR, hxy⟩ := hcover x hx
    simp only [Set.mem_iUnion]
    exact ⟨y, ⟨by simpa using hyR, hx, hxy⟩⟩
  calc
    L.encard ≤ (⋃ y ∈ hR.toFinset, fiber y).encard := Set.encard_mono hsubset
    _ ≤ ∑ y ∈ hR.toFinset, (fiber y).encard := Finset.set_encard_biUnion_le _ _
    _ ≤ ∑ _y ∈ hR.toFinset, c := by
      gcongr with y hy
      exact hfiber y (by simpa using hy)
    _ = c * R.encard := by
      rw [hR.encard_eq_coe_toFinset_card]
      simp [mul_comm]

/-- Helper for Exercise 5.2: zero-dimensional exposed faces are charged to one-dimensional
superfaces, with the empty face and the zero-dimensional ambient case absorbed by the additive
constant. -/
private lemma zeroDimensionalExposedFaces_encard_le_twice_oneDimensional
    {d : ℕ} {Q : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q) :
    {F : Set (Fin d → ℝ) | IsExposed ℝ Q F ∧ polyhedronDim F = 0}.encard ≤
      2 * {G : Set (Fin d → ℝ) | IsExposed ℝ Q G ∧ polyhedronDim G = 1}.encard + 2 := by
  classical
  let zeroFaces : Set (Set (Fin d → ℝ)) :=
    {F | IsExposed ℝ Q F ∧ polyhedronDim F = 0}
  let vertices : Set (Set (Fin d → ℝ)) :=
    {F | IsExposed ℝ Q F ∧ F.Nonempty ∧ polyhedronDim F = 0}
  let edges : Set (Set (Fin d → ℝ)) :=
    {G | IsExposed ℝ Q G ∧ polyhedronDim G = 1}
  have hzero_subset : zeroFaces ⊆ ({∅} : Set (Set (Fin d → ℝ))) ∪ vertices := by
    intro F hF
    by_cases hF_nonempty : F.Nonempty
    · exact Or.inr ⟨hF.1, hF_nonempty, hF.2⟩
    · have hF_empty : F = ∅ := Set.not_nonempty_iff_eq_empty.mp hF_nonempty
      exact Or.inl (Set.mem_singleton_iff.mpr hF_empty)
  by_cases hQ_nonempty : Q.Nonempty
  · by_cases hQ_dim_zero : polyhedronDim Q = 0
    · obtain ⟨q, hQ_singleton⟩ :=
        exists_eq_singleton_of_nonempty_finrank_direction_affineSpan_eq_zero
          hQ_nonempty (by simpa [polyhedronDim] using hQ_dim_zero)
      have hzero_small : zeroFaces ⊆ ({∅, Q} : Set (Set (Fin d → ℝ))) := by
        intro F hF
        by_cases hF_nonempty : F.Nonempty
        · right
          apply Set.Subset.antisymm hF.1.subset
          intro x hxQ
          have hxq : x = q := by simpa [hQ_singleton] using hxQ
          obtain ⟨y, hyF⟩ := hF_nonempty
          have hyq : y = q := by simpa [hQ_singleton] using hF.1.subset hyF
          simpa [hxq, hyq] using hyF
        · left
          exact Set.not_nonempty_iff_eq_empty.mp hF_nonempty
      calc
        zeroFaces.encard ≤ ({∅, Q} : Set (Set (Fin d → ℝ))).encard :=
          Set.encard_mono hzero_small
        _ ≤ 2 := by
          calc
            ({∅, Q} : Set (Set (Fin d → ℝ))).encard ≤
                ({Q} : Set (Set (Fin d → ℝ))).encard + 1 := Set.encard_insert_le _ _
            _ = 2 := by norm_num
        _ ≤ 2 * edges.encard + 2 := self_le_add_left 2 (2 * edges.encard)
    · have hQ_dim_pos : 1 ≤ polyhedronDim Q := Nat.one_le_iff_ne_zero.mpr hQ_dim_zero
      have hedges_finite : edges.Finite :=
        (polyhedron_finite_faces hQ).subset (fun _ hG ↦ hG.1)
      have hvertices_bound : vertices.encard ≤ 2 * edges.encard := by
        apply finiteIncidenceEncard_le (R := edges)
          (Inc := fun F G ↦ F ⊆ G) hedges_finite
        · intro F hF
          obtain ⟨G, hG_exposed, hFG, hG_dim⟩ :=
            exists_oneDimensional_exposed_superface hQ hF.2.1 hF.1 hF.2.2 hQ_dim_pos
          exact ⟨G, ⟨hG_exposed, hG_dim⟩, hFG⟩
        · intro G hG
          simpa only [vertices, Set.mem_setOf_eq, and_assoc, and_left_comm, and_comm] using
            oneDimensionalExposedFace_zeroSubfaces_encard_le_two
              hQ hG.1 hG.2
      calc
        zeroFaces.encard ≤
            (({∅} : Set (Set (Fin d → ℝ))) ∪ vertices).encard :=
          Set.encard_mono hzero_subset
        _ ≤ ({∅} : Set (Set (Fin d → ℝ))).encard + vertices.encard :=
          Set.encard_union_le _ _
        _ ≤ 2 * edges.encard + 1 := by
          simpa [add_comm] using add_le_add_left hvertices_bound 1
        _ ≤ 2 * edges.encard + 2 := by
          exact add_le_add_right (show (1 : ℕ∞) ≤ 2 by norm_num) (2 * edges.encard)
  · have hQ_empty : Q = ∅ := Set.not_nonempty_iff_eq_empty.mp hQ_nonempty
    have hzero_small : zeroFaces ⊆ ({∅} : Set (Set (Fin d → ℝ))) := by
      intro F hF
      have : F = ∅ := by
        apply Set.not_nonempty_iff_eq_empty.mp
        rintro ⟨x, hxF⟩
        have hxQ := hF.1.subset hxF
        simp [hQ_empty] at hxQ
      simp [this]
    calc
      zeroFaces.encard ≤ ({∅} : Set (Set (Fin d → ℝ))).encard :=
        Set.encard_mono hzero_small
      _ ≤ 1 := by simp
      _ ≤ 2 := by norm_num
      _ ≤ 2 * edges.encard + 2 := self_le_add_left 2 (2 * edges.encard)

/-- Helper for Exercise 5.2: a nonempty exposed face of codimension two is contained in at most
two facets.  The proof restricts the active facet rows to the ambient affine direction and then
uses the two-dimensional annihilator of the face direction. -/
private lemma codimTwoExposedFace_superfacets_encard_le_two
    {d : ℕ} {Q G : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q)
    (hG_nonempty : G.Nonempty)
    (hG_exposed : IsExposed ℝ Q G)
    (hcodim : polyhedronDim G + 2 = polyhedronDim Q) :
    {F : Set (Fin d → ℝ) | IsFacetOf Q F ∧ G ⊆ F}.encard ≤ (2 : ℕ∞) := by
  classical
  let facets : Set (Set (Fin d → ℝ)) :=
    {F | IsFacetOf Q F ∧ G ⊆ F}
  have hfacets_finite : facets.Finite :=
    (polyhedron_finite_faces hQ).subset (fun _ hF ↦ hF.1.2.1)
  change facets.encard ≤ (2 : ℕ∞)
  refine (Set.encard_le_coe_iff_finite_ncard_le (s := facets) (k := 2)).2
    ⟨hfacets_finite, ?_⟩
  by_contra hle
  have hthree : 2 < facets.ncard := lt_of_not_ge hle
  obtain ⟨F₁, hF₁, F₂, hF₂, F₃, hF₃, hF₁F₂, hF₁F₃, hF₂F₃⟩ :=
    (Set.two_lt_ncard (s := facets) hfacets_finite).mp hthree
  rcases hQ with ⟨m, A, b, rfl⟩
  rcases exists_equivalent_row_irredundant_representation A b with
    ⟨A', b', hsystem, hirredundant⟩
  have hP_nonempty : (polyhedron_le_set A' b').Nonempty := by
    rw [hsystem]
    exact hG_nonempty.mono hG_exposed.subset
  have hG_exposed' : IsExposed ℝ (polyhedron_le_set A' b') G := by
    rw [hsystem]
    exact hG_exposed
  have hF₁' : IsFacetOf (polyhedron_le_set A' b') F₁ := by
    rw [hsystem]
    exact hF₁.1
  have hF₂' : IsFacetOf (polyhedron_le_set A' b') F₂ := by
    rw [hsystem]
    exact hF₂.1
  have hF₃' : IsFacetOf (polyhedron_le_set A' b') F₃ := by
    rw [hsystem]
    exact hF₃.1
  have hfacet₁ : is_facet (polyhedron_le_set A' b') F₁ :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A' b' hP_nonempty F₁ hF₁'.2.1).2 ⟨hF₁'.1, hF₁'.2.2⟩
  have hfacet₂ : is_facet (polyhedron_le_set A' b') F₂ :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A' b' hP_nonempty F₂ hF₂'.2.1).2 ⟨hF₂'.1, hF₂'.2.2⟩
  have hfacet₃ : is_facet (polyhedron_le_set A' b') F₃ :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A' b' hP_nonempty F₃ hF₃'.2.1).2 ⟨hF₃'.1, hF₃'.2.2⟩
  obtain ⟨j₁, hj₁⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet A' b' hP_nonempty F₁ hfacet₁
  obtain ⟨j₂, hj₂⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet A' b' hP_nonempty F₂ hfacet₂
  obtain ⟨j₃, hj₃⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet A' b' hP_nonempty F₃ hfacet₃
  have hj₁j₂ : j₁.1 ≠ j₂.1 := by
    intro h
    apply hF₁F₂
    rw [hj₁, hj₂, h]
  have hj₁j₃ : j₁.1 ≠ j₃.1 := by
    intro h
    apply hF₁F₃
    rw [hj₁, hj₃, h]
  have hj₂j₃ : j₂.1 ≠ j₃.1 := by
    intro h
    apply hF₂F₃
    rw [hj₂, hj₃, h]
  have hj₁_notImplicit : ¬ is_implicit_equality A' b' j₁.1 :=
    (mem_remaining_inequality_indices_iff A' b' j₁.1).1 j₁.2
  have hj₂_notImplicit : ¬ is_implicit_equality A' b' j₂.1 :=
    (mem_remaining_inequality_indices_iff A' b' j₂.1).1 j₂.2
  have hj₃_notImplicit : ¬ is_implicit_equality A' b' j₃.1 :=
    (mem_remaining_inequality_indices_iff A' b' j₃.1).1 j₃.2
  obtain ⟨x₁, hx₁face, hx₁strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A' b' j₁.1 hP_nonempty (hirredundant j₁.1 hj₁_notImplicit)
  obtain ⟨x₂, hx₂face, hx₂strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A' b' j₂.1 hP_nonempty (hirredundant j₂.1 hj₂_notImplicit)
  obtain ⟨x₃, hx₃face, hx₃strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A' b' j₃.1 hP_nonempty (hirredundant j₃.1 hj₃_notImplicit)
  obtain ⟨x₀, hx₀G⟩ := hG_nonempty
  have hG₁ : G ⊆ active_constraint_face A' b' ({j₁.1} : Set (Fin m)) := by
    rw [← hj₁]
    exact hF₁.2
  have hG₂ : G ⊆ active_constraint_face A' b' ({j₂.1} : Set (Fin m)) := by
    rw [← hj₂]
    exact hF₂.2
  have hG₃ : G ⊆ active_constraint_face A' b' ({j₃.1} : Set (Fin m)) := by
    rw [← hj₃]
    exact hF₃.2
  let DP : Submodule ℝ (Fin d → ℝ) :=
    (affineSpan ℝ (polyhedron_le_set A' b')).direction
  let DG : Submodule ℝ (Fin d → ℝ) := (affineSpan ℝ G).direction
  have hDGDP : DG ≤ DP := by
    exact AffineSubspace.direction_le (affineSpan_mono ℝ hG_exposed'.subset)
  let DG' : Submodule ℝ DP := DG.comap DP.subtype
  let W : Submodule ℝ (Module.Dual ℝ DP) := DG'.dualAnnihilator
  have hDG'_finrank : Module.finrank ℝ DG' = Module.finrank ℝ DG := by
    have hmap : DG'.map DP.subtype = DG := by
      dsimp [DG']
      rw [Submodule.map_comap_subtype, inf_of_le_right hDGDP]
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  have hW_finrank : Module.finrank ℝ W = 2 := by
    have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq DG'
    have hcodim' : Module.finrank ℝ DG + 2 = Module.finrank ℝ DP := by
      have hcodimQ' :
          polyhedronDim G + 2 = polyhedronDim (polyhedron_le_set A' b') := by
        rw [hsystem]
        exact hcodim
      simpa [polyhedronDim, DG, DP] using hcodimQ'
    dsimp [W] at ⊢
    omega
  have hrow_mem (j : Fin m)
      (hGj : G ⊆ active_constraint_face A' b' ({j} : Set (Fin m))) :
      ((dotProductStrongDual (A' j)).toLinearMap.domRestrict DP) ∈
        DG'.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    have hzDG : ((z : DP) : Fin d → ℝ) ∈ DG := by
      simpa [DG'] using hz
    have hx₀aff : x₀ ∈ affineSpan ℝ G := subset_affineSpan ℝ G hx₀G
    rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀aff] at hzDG
    rcases hzDG with ⟨y, hyAff, hyz⟩
    have hGhyper : G ⊆ {x : Fin d → ℝ | A' j ⬝ᵥ x = b' j} := by
      intro x hxG
      exact (mem_active_constraint_face_iff.mp (hGj hxG)).1 j (by simp)
    have hAffHyper := affineSpan_subset_hyperplane_of_subset hGhyper
    have hyRow : A' j ⬝ᵥ y = b' j := hAffHyper hyAff
    have hx₀Row : A' j ⬝ᵥ x₀ = b' j := hAffHyper hx₀aff
    simp only [LinearMap.domRestrict_apply]
    rw [hyz]
    exact (show dotProductStrongDual (A' j) (y -ᵥ x₀) = 0 by
      simp [dotProductStrongDual_apply, vsub_eq_sub, hyRow, hx₀Row])
  let row₁ : W := ⟨(dotProductStrongDual (A' j₁.1)).toLinearMap.domRestrict DP,
    hrow_mem j₁.1 hG₁⟩
  let row₂ : W := ⟨(dotProductStrongDual (A' j₂.1)).toLinearMap.domRestrict DP,
    hrow_mem j₂.1 hG₂⟩
  let row₃ : W := ⟨(dotProductStrongDual (A' j₃.1)).toLinearMap.domRestrict DP,
    hrow_mem j₃.1 hG₃⟩
  have hx₁P : x₁ ∈ polyhedron_le_set A' b' :=
    mem_polyhedron_of_mem_active_constraint_face hx₁face
  have hx₂P : x₂ ∈ polyhedron_le_set A' b' :=
    mem_polyhedron_of_mem_active_constraint_face hx₂face
  have hx₃P : x₃ ∈ polyhedron_le_set A' b' :=
    mem_polyhedron_of_mem_active_constraint_face hx₃face
  have hx₀P : x₀ ∈ polyhedron_le_set A' b' := hG_exposed'.subset hx₀G
  have hdiff_mem (x : Fin d → ℝ) (hx : x ∈ polyhedron_le_set A' b') :
      x - x₀ ∈ DP := by
    simpa [DP, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ hx) (subset_affineSpan ℝ _ hx₀P)
  let evalAt (x : Fin d → ℝ) (hx : x ∈ polyhedron_le_set A' b') :
      Module.Dual ℝ W :=
    (Module.Dual.eval ℝ DP ⟨x - x₀, hdiff_mem x hx⟩).domRestrict W
  have heval (x : Fin d → ℝ) (hx : x ∈ polyhedron_le_set A' b')
      (j : Fin m) (hGj : G ⊆ active_constraint_face A' b' ({j} : Set (Fin m))) :
      evalAt x hx ⟨(dotProductStrongDual (A' j)).toLinearMap.domRestrict DP,
          hrow_mem j hGj⟩ =
        (A' *ᵥ x) j - b' j := by
    have hx₀Row : (A' *ᵥ x₀) j = b' j :=
      (mem_active_constraint_face_iff.mp (hGj hx₀G)).1 j (by simp)
    have hx₀RowDot : A' j ⬝ᵥ x₀ = b' j := by
      simpa [Matrix.mulVec] using hx₀Row
    simp [evalAt, dotProductStrongDual_apply, Matrix.mulVec, hx₀RowDot]
  have hx₁eq : (A' *ᵥ x₁) j₁.1 = b' j₁.1 :=
    (mem_active_constraint_face_iff.mp hx₁face).1 j₁.1 (by simp)
  have hx₂eq : (A' *ᵥ x₂) j₂.1 = b' j₂.1 :=
    (mem_active_constraint_face_iff.mp hx₂face).1 j₂.1 (by simp)
  have hx₃eq : (A' *ᵥ x₃) j₃.1 = b' j₃.1 :=
    (mem_active_constraint_face_iff.mp hx₃face).1 j₃.1 (by simp)
  have h₁₂ : (A' *ᵥ x₁) j₂.1 < b' j₂.1 :=
    hx₁strict j₂.1 (Ne.symm hj₁j₂) hj₂_notImplicit
  have h₁₃ : (A' *ᵥ x₁) j₃.1 < b' j₃.1 :=
    hx₁strict j₃.1 (Ne.symm hj₁j₃) hj₃_notImplicit
  have h₂₁ : (A' *ᵥ x₂) j₁.1 < b' j₁.1 :=
    hx₂strict j₁.1 hj₁j₂ hj₁_notImplicit
  have h₂₃ : (A' *ᵥ x₂) j₃.1 < b' j₃.1 :=
    hx₂strict j₃.1 (Ne.symm hj₂j₃) hj₃_notImplicit
  have h₃₁ : (A' *ᵥ x₃) j₁.1 < b' j₁.1 :=
    hx₃strict j₁.1 hj₁j₃ hj₁_notImplicit
  have h₃₂ : (A' *ᵥ x₃) j₂.1 < b' j₂.1 :=
    hx₃strict j₂.1 hj₂j₃ hj₂_notImplicit
  have he₁₁ : evalAt x₁ hx₁P row₁ = 0 := by
    dsimp only [row₁]
    rw [heval x₁ hx₁P j₁.1 hG₁]
    exact sub_eq_zero.mpr hx₁eq
  have he₂₁ : evalAt x₂ hx₂P row₁ < 0 := by
    dsimp only [row₁]
    rw [heval x₂ hx₂P j₁.1 hG₁]
    exact sub_neg.mpr h₂₁
  have he₃₁ : evalAt x₃ hx₃P row₁ < 0 := by
    dsimp only [row₁]
    rw [heval x₃ hx₃P j₁.1 hG₁]
    exact sub_neg.mpr h₃₁
  have he₁₂ : evalAt x₁ hx₁P row₂ < 0 := by
    dsimp only [row₂]
    rw [heval x₁ hx₁P j₂.1 hG₂]
    exact sub_neg.mpr h₁₂
  have he₂₂ : evalAt x₂ hx₂P row₂ = 0 := by
    dsimp only [row₂]
    rw [heval x₂ hx₂P j₂.1 hG₂]
    exact sub_eq_zero.mpr hx₂eq
  have he₃₂ : evalAt x₃ hx₃P row₂ < 0 := by
    dsimp only [row₂]
    rw [heval x₃ hx₃P j₂.1 hG₂]
    exact sub_neg.mpr h₃₂
  have he₁₃ : evalAt x₁ hx₁P row₃ < 0 := by
    dsimp only [row₃]
    rw [heval x₁ hx₁P j₃.1 hG₃]
    exact sub_neg.mpr h₁₃
  have he₂₃ : evalAt x₂ hx₂P row₃ < 0 := by
    dsimp only [row₃]
    rw [heval x₂ hx₂P j₃.1 hG₃]
    exact sub_neg.mpr h₂₃
  have he₃₃ : evalAt x₃ hx₃P row₃ = 0 := by
    dsimp only [row₃]
    rw [heval x₃ hx₃P j₃.1 hG₃]
    exact sub_eq_zero.mpr hx₃eq
  -- The three strict-row witnesses give the forbidden sign pattern in a two-dimensional space.
  exact three_functionals_not_pairwise_exclusive hW_finrank.le
    (evalAt x₁ hx₁P) (evalAt x₂ hx₂P) (evalAt x₃ hx₃P)
    row₁ row₂ row₃ he₁₁ he₂₁ he₃₁ he₁₂ he₂₂ he₃₂ he₁₃ he₂₃ he₃₃

/-- Helper for Exercise 5.2: lineality directions of a nonempty set lie in the direction of its
affine span. -/
private lemma linealitySubmodule_le_affineSpanDirection_of_nonempty
    {d : ℕ} {Q : Set (Fin d → ℝ)} (hQ_nonempty : Q.Nonempty) :
    linealitySubmodule Q ≤ (affineSpan ℝ Q).direction := by
  intro r hr
  obtain ⟨x₀, hx₀Q⟩ := hQ_nonempty
  have hx₀aff : x₀ ∈ affineSpan ℝ Q := subset_affineSpan ℝ Q hx₀Q
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff] at hr
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀aff]
  -- Translating a base point by a lineality direction realizes that direction in the affine span.
  refine ⟨x₀ + r, subset_affineSpan ℝ Q (by simpa using hr hx₀Q 1), ?_⟩
  ext i
  simp

/-- Helper for Exercise 5.2: if `L ≤ D` has codimension at most one in `D`, then the annihilator
of `L` inside the dual of `D` has dimension at most one. -/
private lemma dualAnnihilator_finrank_le_one
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (D L : Submodule ℝ V) (hLD : L ≤ D)
    (hdim : Module.finrank ℝ D ≤ Module.finrank ℝ L + 1) :
    Module.finrank ℝ ((L.comap D.subtype).dualAnnihilator) ≤ 1 := by
  let L' : Submodule ℝ D := L.comap D.subtype
  have hmap : L'.map D.subtype = L := by
    dsimp [L']
    rw [Submodule.map_comap_subtype, inf_of_le_right hLD]
  have hL'_finrank : Module.finrank ℝ L' = Module.finrank ℝ L := by
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  have hann := Subspace.finrank_add_finrank_dualAnnihilator_eq L'
  -- The annihilator dimension is exactly the remaining codimension.
  dsimp [L'] at hL'_finrank hann ⊢
  omega

/-- Helper for Exercise 5.2: three affine boundary points in the dual of a space of dimension at
most one cannot be mutually exclusive for three evaluation functionals. -/
private lemma threeDualAffinePoints_not_pairwise_exclusive
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V ≤ 1)
    (row₁ row₂ row₃ : V) (r₁ r₂ r₃ : ℝ)
    (f₁ f₂ f₃ : Module.Dual ℝ V) (hf₁f₂ : f₁ ≠ f₂)
    (h₁₁ : f₁ row₁ = r₁) (h₁₂ : f₁ row₂ < r₂) (h₁₃ : f₁ row₃ < r₃)
    (h₂₁ : f₂ row₁ < r₁) (h₂₂ : f₂ row₂ = r₂) (h₂₃ : f₂ row₃ < r₃)
    (h₃₁ : f₃ row₁ < r₁) (h₃₂ : f₃ row₂ < r₂) (h₃₃ : f₃ row₃ = r₃) : False := by
  -- Evaluate at the three rows and invoke the one-dimensional affine obstruction.
  apply three_affine_functionals_not_pairwise_exclusive
    (dual_finrank_le_one_of_finrank_le_one hdim)
    (Module.Dual.eval ℝ V row₁) (Module.Dual.eval ℝ V row₂)
    (Module.Dual.eval ℝ V row₃) r₁ r₂ r₃ f₁ f₂ f₃ hf₁f₂
  · simpa only [Module.Dual.eval_apply] using h₁₁
  · simpa only [Module.Dual.eval_apply] using h₁₂
  · simpa only [Module.Dual.eval_apply] using h₁₃
  · simpa only [Module.Dual.eval_apply] using h₂₁
  · simpa only [Module.Dual.eval_apply] using h₂₂
  · simpa only [Module.Dual.eval_apply] using h₂₃
  · simpa only [Module.Dual.eval_apply] using h₃₁
  · simpa only [Module.Dual.eval_apply] using h₃₂
  · simpa only [Module.Dual.eval_apply] using h₃₃

/-- Helper for Exercise 5.2: three distinct active rows cannot have mutually exclusive tight
points when the polyhedron modulo its lineality has dimension at most one. -/
private lemma threeActiveRows_impossible_of_smallQuotient
    {m d : ℕ} (A : Matrix (Fin m) (Fin d) ℝ) (b : Fin m → ℝ)
    (hP_nonempty : (polyhedron_le_set A b).Nonempty)
    (hdim : polyhedronDim (polyhedron_le_set A b) ≤
      Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) + 1)
    {j₁ j₂ j₃ : Fin m}
    (hj₁j₂ : j₁ ≠ j₂) (hj₁j₃ : j₁ ≠ j₃) (hj₂j₃ : j₂ ≠ j₃)
    (hj₁_notImplicit : ¬ is_implicit_equality A b j₁)
    (hj₂_notImplicit : ¬ is_implicit_equality A b j₂)
    (hj₃_notImplicit : ¬ is_implicit_equality A b j₃)
    {x₁ x₂ x₃ : Fin d → ℝ}
    (hx₁face : x₁ ∈ active_constraint_face A b ({j₁} : Set (Fin m)))
    (hx₂face : x₂ ∈ active_constraint_face A b ({j₂} : Set (Fin m)))
    (hx₃face : x₃ ∈ active_constraint_face A b ({j₃} : Set (Fin m)))
    (hx₁strict : ∀ i : Fin m, i ≠ j₁ → ¬ is_implicit_equality A b i → (A *ᵥ x₁) i < b i)
    (hx₂strict : ∀ i : Fin m, i ≠ j₂ → ¬ is_implicit_equality A b i → (A *ᵥ x₂) i < b i)
    (hx₃strict : ∀ i : Fin m, i ≠ j₃ → ¬ is_implicit_equality A b i → (A *ᵥ x₃) i < b i) :
    False := by
  obtain ⟨x₀, hx₀P⟩ := hP_nonempty
  let DP : Submodule ℝ (Fin d → ℝ) :=
    (affineSpan ℝ (polyhedron_le_set A b)).direction
  let L : Submodule ℝ (Fin d → ℝ) := linealitySubmodule (polyhedron_le_set A b)
  have hLDP : L ≤ DP :=
    linealitySubmodule_le_affineSpanDirection_of_nonempty ⟨x₀, hx₀P⟩
  let L' : Submodule ℝ DP := L.comap DP.subtype
  let W : Submodule ℝ (Module.Dual ℝ DP) := L'.dualAnnihilator
  have hdimDP : Module.finrank ℝ DP ≤ Module.finrank ℝ L + 1 := by
    simpa [polyhedronDim, DP, L] using hdim
  have hW_finrank : Module.finrank ℝ W ≤ 1 := by
    simpa only [W, L'] using dualAnnihilator_finrank_le_one DP L hLDP hdimDP
  have hrow_mem (j : Fin m) :
      ((dotProductStrongDual (A j)).toLinearMap.domRestrict DP) ∈
        L'.dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    have hzL : ((z : DP) : Fin d → ℝ) ∈ L := by
      simpa [L'] using hz
    rw [mem_linealitySubmodule_iff,
      polyhedron_linealitySpace_eq_kernel_set A b ⟨x₀, hx₀P⟩] at hzL
    have hzRow : (A *ᵥ ((z : DP) : Fin d → ℝ)) j = 0 := congrFun hzL j
    simpa [Matrix.mulVec, dotProductStrongDual_apply] using hzRow
  let row₁ : W :=
    ⟨(dotProductStrongDual (A j₁)).toLinearMap.domRestrict DP, hrow_mem j₁⟩
  let row₂ : W :=
    ⟨(dotProductStrongDual (A j₂)).toLinearMap.domRestrict DP, hrow_mem j₂⟩
  let row₃ : W :=
    ⟨(dotProductStrongDual (A j₃)).toLinearMap.domRestrict DP, hrow_mem j₃⟩
  have hx₁P : x₁ ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hx₁face
  have hx₂P : x₂ ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hx₂face
  have hx₃P : x₃ ∈ polyhedron_le_set A b :=
    mem_polyhedron_of_mem_active_constraint_face hx₃face
  have hdiff_mem (x : Fin d → ℝ) (hx : x ∈ polyhedron_le_set A b) : x - x₀ ∈ DP := by
    simpa [DP, vsub_eq_sub] using
      AffineSubspace.vsub_mem_direction
        (subset_affineSpan ℝ _ hx) (subset_affineSpan ℝ _ hx₀P)
  let evalAt (x : Fin d → ℝ) (hx : x ∈ polyhedron_le_set A b) : Module.Dual ℝ W :=
    (Module.Dual.eval ℝ DP ⟨x - x₀, hdiff_mem x hx⟩).domRestrict W
  have heval (x : Fin d → ℝ) (hx : x ∈ polyhedron_le_set A b) (j : Fin m) :
      evalAt x hx ⟨(dotProductStrongDual (A j)).toLinearMap.domRestrict DP, hrow_mem j⟩ =
        (A *ᵥ x) j - (A *ᵥ x₀) j := by
    simp [evalAt, dotProductStrongDual_apply, Matrix.mulVec]
  let r₁ : ℝ := b j₁ - (A *ᵥ x₀) j₁
  let r₂ : ℝ := b j₂ - (A *ᵥ x₀) j₂
  let r₃ : ℝ := b j₃ - (A *ᵥ x₀) j₃
  have hx₁eq : (A *ᵥ x₁) j₁ = b j₁ :=
    (mem_active_constraint_face_iff.mp hx₁face).1 j₁ (by simp)
  have hx₂eq : (A *ᵥ x₂) j₂ = b j₂ :=
    (mem_active_constraint_face_iff.mp hx₂face).1 j₂ (by simp)
  have hx₃eq : (A *ᵥ x₃) j₃ = b j₃ :=
    (mem_active_constraint_face_iff.mp hx₃face).1 j₃ (by simp)
  have h₁₂ : (A *ᵥ x₁) j₂ < b j₂ := hx₁strict j₂ (Ne.symm hj₁j₂) hj₂_notImplicit
  have h₁₃ : (A *ᵥ x₁) j₃ < b j₃ := hx₁strict j₃ (Ne.symm hj₁j₃) hj₃_notImplicit
  have h₂₁ : (A *ᵥ x₂) j₁ < b j₁ := hx₂strict j₁ hj₁j₂ hj₁_notImplicit
  have h₂₃ : (A *ᵥ x₂) j₃ < b j₃ := hx₂strict j₃ (Ne.symm hj₂j₃) hj₃_notImplicit
  have h₃₁ : (A *ᵥ x₃) j₁ < b j₁ := hx₃strict j₁ hj₁j₃ hj₁_notImplicit
  have h₃₂ : (A *ᵥ x₃) j₂ < b j₂ := hx₃strict j₂ hj₂j₃ hj₂_notImplicit
  have he₁₁ : evalAt x₁ hx₁P row₁ = r₁ := by
    dsimp only [row₁, r₁]
    rw [heval x₁ hx₁P j₁]
    linarith
  have he₂₁ : evalAt x₂ hx₂P row₁ < r₁ := by
    dsimp only [row₁, r₁]
    rw [heval x₂ hx₂P j₁]
    linarith
  have he₃₁ : evalAt x₃ hx₃P row₁ < r₁ := by
    dsimp only [row₁, r₁]
    rw [heval x₃ hx₃P j₁]
    linarith
  have he₁₂ : evalAt x₁ hx₁P row₂ < r₂ := by
    dsimp only [row₂, r₂]
    rw [heval x₁ hx₁P j₂]
    linarith
  have he₂₂ : evalAt x₂ hx₂P row₂ = r₂ := by
    dsimp only [row₂, r₂]
    rw [heval x₂ hx₂P j₂]
    linarith
  have he₃₂ : evalAt x₃ hx₃P row₂ < r₂ := by
    dsimp only [row₂, r₂]
    rw [heval x₃ hx₃P j₂]
    linarith
  have he₁₃ : evalAt x₁ hx₁P row₃ < r₃ := by
    dsimp only [row₃, r₃]
    rw [heval x₁ hx₁P j₃]
    linarith
  have he₂₃ : evalAt x₂ hx₂P row₃ < r₃ := by
    dsimp only [row₃, r₃]
    rw [heval x₂ hx₂P j₃]
    linarith
  have he₃₃ : evalAt x₃ hx₃P row₃ = r₃ := by
    dsimp only [row₃, r₃]
    rw [heval x₃ hx₃P j₃]
    linarith
  have heval₁_ne_eval₂ : evalAt x₁ hx₁P ≠ evalAt x₂ hx₂P := by
    intro heq
    have h₁ := congrArg (fun f : Module.Dual ℝ W ↦ f row₁) heq
    linarith
  -- The restricted rows would realize three mutually exclusive affine boundary points.
  exact threeDualAffinePoints_not_pairwise_exclusive hW_finrank row₁ row₂ row₃ r₁ r₂ r₃
    (evalAt x₁ hx₁P) (evalAt x₂ hx₂P) (evalAt x₃ hx₃P) heval₁_ne_eval₂
    he₁₁ he₁₂ he₁₃ he₂₁ he₂₂ he₂₃ he₃₁ he₃₂ he₃₃

/-- Helper for Exercise 5.2: a nonempty polyhedron whose quotient by lineality has dimension at
most one has at most two facets. -/
private lemma facets_encard_le_two_of_polyhedronDim_le_lineality_add_one
    {d : ℕ} {Q : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q) (hQ_nonempty : Q.Nonempty)
    (hdim : polyhedronDim Q ≤ Module.finrank ℝ (linealitySubmodule Q) + 1) :
    {F : Set (Fin d → ℝ) | IsFacetOf Q F}.encard ≤ (2 : ℕ∞) := by
  classical
  let facets : Set (Set (Fin d → ℝ)) := {F | IsFacetOf Q F}
  have hfacets_finite : facets.Finite :=
    (polyhedron_finite_faces hQ).subset (fun _ hF ↦ hF.2.1)
  change facets.encard ≤ (2 : ℕ∞)
  refine (Set.encard_le_coe_iff_finite_ncard_le (s := facets) (k := 2)).2
    ⟨hfacets_finite, ?_⟩
  by_contra hle
  have hthree : 2 < facets.ncard := lt_of_not_ge hle
  obtain ⟨F₁, hF₁, F₂, hF₂, F₃, hF₃, hF₁F₂, hF₁F₃, hF₂F₃⟩ :=
    (Set.two_lt_ncard (s := facets) hfacets_finite).mp hthree
  rcases hQ with ⟨m, A, b, rfl⟩
  rcases exists_equivalent_row_irredundant_representation A b with
    ⟨A', b', hsystem, hirredundant⟩
  have hP_nonempty : (polyhedron_le_set A' b').Nonempty := by
    rwa [hsystem]
  have hdim' :
      polyhedronDim (polyhedron_le_set A' b') ≤
        Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A' b')) + 1 := by
    rw [hsystem]
    exact hdim
  have hF₁' : IsFacetOf (polyhedron_le_set A' b') F₁ := by
    rw [hsystem]
    exact hF₁
  have hF₂' : IsFacetOf (polyhedron_le_set A' b') F₂ := by
    rw [hsystem]
    exact hF₂
  have hF₃' : IsFacetOf (polyhedron_le_set A' b') F₃ := by
    rw [hsystem]
    exact hF₃
  have hfacet₁ : is_facet (polyhedron_le_set A' b') F₁ :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A' b' hP_nonempty F₁ hF₁'.2.1).2 ⟨hF₁'.1, hF₁'.2.2⟩
  have hfacet₂ : is_facet (polyhedron_le_set A' b') F₂ :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A' b' hP_nonempty F₂ hF₂'.2.1).2 ⟨hF₂'.1, hF₂'.2.2⟩
  have hfacet₃ : is_facet (polyhedron_le_set A' b') F₃ :=
    (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
      A' b' hP_nonempty F₃ hF₃'.2.1).2 ⟨hF₃'.1, hF₃'.2.2⟩
  obtain ⟨j₁, hj₁⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet A' b' hP_nonempty F₁ hfacet₁
  obtain ⟨j₂, hj₂⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet A' b' hP_nonempty F₂ hfacet₂
  obtain ⟨j₃, hj₃⟩ :=
    exists_eq_active_constraint_face_singleton_of_is_facet A' b' hP_nonempty F₃ hfacet₃
  have hj₁j₂ : j₁.1 ≠ j₂.1 := by
    intro h
    apply hF₁F₂
    rw [hj₁, hj₂, h]
  have hj₁j₃ : j₁.1 ≠ j₃.1 := by
    intro h
    apply hF₁F₃
    rw [hj₁, hj₃, h]
  have hj₂j₃ : j₂.1 ≠ j₃.1 := by
    intro h
    apply hF₂F₃
    rw [hj₂, hj₃, h]
  have hj₁_notImplicit : ¬ is_implicit_equality A' b' j₁.1 :=
    (mem_remaining_inequality_indices_iff A' b' j₁.1).1 j₁.2
  have hj₂_notImplicit : ¬ is_implicit_equality A' b' j₂.1 :=
    (mem_remaining_inequality_indices_iff A' b' j₂.1).1 j₂.2
  have hj₃_notImplicit : ¬ is_implicit_equality A' b' j₃.1 :=
    (mem_remaining_inequality_indices_iff A' b' j₃.1).1 j₃.2
  obtain ⟨x₁, hx₁face, hx₁strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A' b' j₁.1 hP_nonempty (hirredundant j₁.1 hj₁_notImplicit)
  obtain ⟨x₂, hx₂face, hx₂strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A' b' j₂.1 hP_nonempty (hirredundant j₂.1 hj₂_notImplicit)
  obtain ⟨x₃, hx₃face, hx₃strict⟩ :=
    exists_point_in_active_constraint_face_singleton_strict_on_other_nonimplicit_rows
      A' b' j₃.1 hP_nonempty (hirredundant j₃.1 hj₃_notImplicit)
  -- Pass the three strict witnesses to the quotient argument in a fresh declaration budget.
  exact threeActiveRows_impossible_of_smallQuotient A' b' hP_nonempty hdim'
    hj₁j₂ hj₁j₃ hj₂j₃ hj₁_notImplicit hj₂_notImplicit hj₃_notImplicit
    hx₁face hx₂face hx₃face hx₁strict hx₂strict hx₃strict

/-- Helper for Exercise 5.2: exposed faces in the two ambient top ranks are controlled by
codimension-two faces.  The ambient face costs one; facets are either the two boundary facets of
a one-dimensional quotient or are charged to a codimension-two subface. -/
private lemma ambientTopExposedFaces_encard_le_twice_codimTwo
    {d : ℕ} {Q : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q) (hd : 3 ≤ d) :
    {F : Set (Fin d → ℝ) | IsExposed ℝ Q F ∧ d - 1 ≤ polyhedronDim F}.encard ≤
      2 * {G : Set (Fin d → ℝ) | IsExposed ℝ Q G ∧ polyhedronDim G = d - 2}.encard + 3 := by
  classical
  let topFaces : Set (Set (Fin d → ℝ)) :=
    {F | IsExposed ℝ Q F ∧ d - 1 ≤ polyhedronDim F}
  let facets : Set (Set (Fin d → ℝ)) := {F | IsFacetOf Q F}
  let ridges : Set (Set (Fin d → ℝ)) :=
    {G | IsExposed ℝ Q G ∧ polyhedronDim G = d - 2}
  have hEmptyDim : polyhedronDim (∅ : Set (Fin d → ℝ)) = 0 := by
    rw [polyhedronDim, (affineSpan_eq_bot (k := ℝ) (s := (∅ : Set (Fin d → ℝ)))).2 rfl,
      AffineSubspace.direction_bot, finrank_bot]
  have hQdim_le_d : polyhedronDim Q ≤ d := by
    rw [polyhedronDim]
    have hmono := Submodule.finrank_mono
      (show (affineSpan ℝ Q).direction ≤ (⊤ : Submodule ℝ (Fin d → ℝ)) from le_top)
    calc
      Module.finrank ℝ (affineSpan ℝ Q).direction ≤ Module.finrank ℝ (Fin d → ℝ) := by
        simpa only [finrank_top] using hmono
      _ = d := by simp
  by_cases hfull : polyhedronDim Q = d
  · have hQ_nonempty : Q.Nonempty := by
      apply Set.nonempty_iff_ne_empty.mpr
      intro hQempty
      rw [hQempty, hEmptyDim] at hfull
      omega
    have htop_subset : topFaces ⊆ ({Q} : Set (Set (Fin d → ℝ))) ∪ facets := by
      intro F hF
      by_cases hFQ : F = Q
      · exact Or.inl (Set.mem_singleton_iff.mpr hFQ)
      · have hF_nonempty : F.Nonempty := by
          apply Set.nonempty_iff_ne_empty.mpr
          intro hFempty
          have hFdim_lower : d - 1 ≤ polyhedronDim F := hF.2
          rw [hFempty, hEmptyDim] at hFdim_lower
          omega
        have hFproper : F ⊂ Q := hF.1.subset.ssubset_of_ne hFQ
        have hdim_le :=
          finrank_direction_affineSpan_le_sub_one_of_ssubset
            hQ hF.1 (IsExposed.refl Q) hFproper
        have hcodim : polyhedronDim F + 1 = polyhedronDim Q := by
          have hFdim_lower : d - 1 ≤ polyhedronDim F := hF.2
          simp only [polyhedronDim] at hdim_le hFdim_lower hfull ⊢
          omega
        exact Or.inr ((isFacetOf_iff).2 ⟨hF_nonempty, hF.1, hcodim⟩)
    have htop_count : topFaces.encard ≤ 1 + facets.encard := by
      calc
        topFaces.encard ≤ (({Q} : Set (Set (Fin d → ℝ))) ∪ facets).encard :=
          Set.encard_mono htop_subset
        _ ≤ ({Q} : Set (Set (Fin d → ℝ))).encard + facets.encard :=
          Set.encard_union_le _ _
        _ = 1 + facets.encard := by rw [Set.encard_singleton]
    by_cases hlineality :
        Module.finrank ℝ (linealitySubmodule Q) ≤ d - 2
    · obtain ⟨m, A, b, hQeq⟩ := hQ
      have hfacets_finite : facets.Finite :=
        (polyhedron_finite_faces ⟨m, A, b, hQeq⟩).subset (fun _ hF ↦ hF.2.1)
      have hridges_finite : ridges.Finite :=
        (polyhedron_finite_faces ⟨m, A, b, hQeq⟩).subset (fun _ hG ↦ hG.1)
      have hfacets_bound : facets.encard ≤ 2 * ridges.encard := by
        apply finiteIncidenceEncard_le (R := ridges) (Inc := fun F G ↦ G ⊆ F)
          hridges_finite
        · intro F hF
          have hFdim : Module.finrank ℝ (affineSpan ℝ F).direction = d - 1 := by
            have hcodim := (isFacetOf_iff.mp hF).2.2
            simpa [polyhedronDim] using (show polyhedronDim F = d - 1 by
              simp only [polyhedronDim] at hcodim hfull ⊢
              omega)
          have hlineality' :
              Module.finrank ℝ (linealitySubmodule (polyhedron_le_set A b)) ≤ d - 2 := by
            rw [← hQeq]
            exact hlineality
          have hkF : d - 2 ≤ Module.finrank ℝ (affineSpan ℝ F).direction := by omega
          have hF_exposed' : IsExposed ℝ (polyhedron_le_set A b) F := by
            rw [← hQeq]
            exact (isFacetOf_iff.mp hF).2.1
          obtain ⟨G, hG_nonempty, hG_exposed, hGF, hGdim⟩ :=
            exists_nonempty_face_of_finrank_between_lineality_and_exposed_face
              A b F (isFacetOf_iff.mp hF).1 hF_exposed' (d - 2) hlineality' hkF
          refine ⟨G, ?_, hGF⟩
          constructor
          · rw [hQeq]
            exact hG_exposed
          · simpa [polyhedronDim] using hGdim
        · intro G hG
          have hG_nonempty : G.Nonempty := by
            apply Set.nonempty_iff_ne_empty.mpr
            intro hGempty
            have hGdim_eq : polyhedronDim G = d - 2 := hG.2
            rw [hGempty, hEmptyDim] at hGdim_eq
            omega
          have hcodimG : polyhedronDim G + 2 = polyhedronDim Q := by
            have hGdim_eq : polyhedronDim G = d - 2 := hG.2
            omega
          simpa only [facets, Set.mem_setOf_eq] using
            codimTwoExposedFace_superfacets_encard_le_two
              ⟨m, A, b, hQeq⟩ hG_nonempty hG.1 hcodimG
      calc
        topFaces.encard ≤ 1 + facets.encard := htop_count
        _ ≤ 1 + 2 * ridges.encard := by gcongr
        _ ≤ 2 * ridges.encard + 3 := by
          simpa [add_comm] using
            add_le_add_left (show (1 : ℕ∞) ≤ 3 by norm_num) (2 * ridges.encard)
    · have hlineality_ge : d - 1 ≤ Module.finrank ℝ (linealitySubmodule Q) := by omega
      have hquotient_dim :
          polyhedronDim Q ≤ Module.finrank ℝ (linealitySubmodule Q) + 1 := by omega
      have hfacets_bound : facets.encard ≤ (2 : ℕ∞) := by
        simpa only [facets] using
          facets_encard_le_two_of_polyhedronDim_le_lineality_add_one
            hQ hQ_nonempty hquotient_dim
      calc
        topFaces.encard ≤ 1 + facets.encard := htop_count
        _ ≤ 1 + 2 := by gcongr
        _ ≤ 2 * ridges.encard + 3 := by
          norm_num
  · have hQdim_le : polyhedronDim Q ≤ d - 1 := by omega
    have htop_subset : topFaces ⊆ ({Q} : Set (Set (Fin d → ℝ))) := by
      intro F hF
      have hFdim_le_Q : polyhedronDim F ≤ polyhedronDim Q := by
        rw [polyhedronDim, polyhedronDim]
        exact Submodule.finrank_mono
          (AffineSubspace.direction_le (affineSpan_mono ℝ hF.1.subset))
      have hFQ : F = Q := by
        by_contra hne
        have hproper : F ⊂ Q := hF.1.subset.ssubset_of_ne hne
        have hdrop :=
          finrank_direction_affineSpan_le_sub_one_of_ssubset
            hQ hF.1 (IsExposed.refl Q) hproper
        have hFdim_lower : d - 1 ≤ polyhedronDim F := hF.2
        simp only [polyhedronDim] at hFdim_lower hQdim_le hFdim_le_Q hdrop
        omega
      simp [hFQ]
    calc
      topFaces.encard ≤ ({Q} : Set (Set (Fin d → ℝ))).encard :=
        Set.encard_mono htop_subset
      _ ≤ 1 := by simp
      _ ≤ 3 := by norm_num
      _ ≤ 2 * ridges.encard + 3 := self_le_add_left 3 (2 * ridges.encard)

/-- Helper for Exercise 5.2: adjoining the lower split inequality to a polyhedral presentation
again gives a polyhedron. -/
private lemma splitBranchLower_isPolyhedron
    {d : ℕ} {Q : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q) (π : Fin d → ℤ) (π0 : ℤ) :
    is_polyhedron (split_branch_lower Q π π0) := by
  rcases hQ with ⟨m, A, b, rfl⟩
  refine ⟨m + 1, Fin.snoc A (fun j ↦ (π j : ℝ)), Fin.snoc b (π0 : ℝ), ?_⟩
  ext x
  rw [mem_split_branch_lower_iff, mem_polyhedron_le_set_iff,
    mem_polyhedron_le_set_iff]
  constructor
  · rintro ⟨hxQ, hxSplit⟩
    -- The old rows recover `Q`, while the final row is precisely the lower split inequality.
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last] using hxSplit
    · simpa [Matrix.mulVec, Fin.snoc_castSucc] using hxQ i
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      simpa [Matrix.mulVec, Fin.snoc_castSucc] using hx i.castSucc
    · simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last] using hx (Fin.last m)

/-- Helper for Exercise 5.2: adjoining the negated upper split inequality to a polyhedral
presentation again gives a polyhedron. -/
private lemma splitBranchUpper_isPolyhedron
    {d : ℕ} {Q : Set (Fin d → ℝ)}
    (hQ : is_polyhedron Q) (π : Fin d → ℤ) (π0 : ℤ) :
    is_polyhedron (split_branch_upper Q π π0) := by
  rcases hQ with ⟨m, A, b, rfl⟩
  refine ⟨m + 1, Fin.snoc A (fun j ↦ -((π j : ℝ))),
    Fin.snoc b (-((π0 : ℝ) + 1)), ?_⟩
  ext x
  rw [mem_split_branch_upper_iff, mem_polyhedron_le_set_iff,
    mem_polyhedron_le_set_iff]
  constructor
  · rintro ⟨hxQ, hxSplit⟩
    -- Negating the upper inequality turns it into the appended `≤` row.
    refine Fin.lastCases ?_ (fun i ↦ ?_)
    · have hlast : -(split_dot π x) ≤ -((π0 : ℝ) + 1) := by linarith
      simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
        Fin.snoc_castSucc, Fin.snoc_last] using hlast
    · simpa [Matrix.mulVec, Fin.snoc_castSucc] using hxQ i
  · intro hx
    refine ⟨?_, ?_⟩
    · intro i
      simpa [Matrix.mulVec, Fin.snoc_castSucc] using hx i.castSucc
    · have hlast : -(split_dot π x) ≤ -((π0 : ℝ) + 1) := by
        simpa [Matrix.mulVec, split_dot, dotProduct, Fin.sum_univ_castSucc,
          Fin.snoc_castSucc, Fin.snoc_last] using hx (Fin.last m)
      linarith

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap05/section_5_6/ch5_sec5_6_exercise_5_2.lean
The two split branches satisfy the endpoint incidence estimates that reduce zero-dimensional
faces to edges and ambient-top faces to codimension-two faces. -/
private lemma splitPair_boundaryFaceCounts_le
    {P Pi1 Pi2 : Set (Fin (n + p) → ℝ)}
    {nFaces1 nFaces2 : ℕ → ℕ}
    (hP : is_polyhedron P)
    (hsplit : exercise_5_2_is_split_pair (n := n) (p := p) P Pi1 Pi2)
    (hambient : 3 ≤ n + p)
    (hFaces1 : exercise_5_2_has_face_counts (n := n) (p := p) Pi1 nFaces1)
    (hFaces2 : exercise_5_2_has_face_counts (n := n) (p := p) Pi2 nFaces2) :
    ((branchZeroFaces (n := n) (p := p) Pi1).encard ≤
        ((2 * nFaces1 1 + 2 : ℕ) : ℕ∞) ∧
      (branchTopFaces (n := n) (p := p) Pi1).encard ≤
        ((2 * nFaces1 (n + p - 2) + 3 : ℕ) : ℕ∞)) ∧
    ((branchZeroFaces (n := n) (p := p) Pi2).encard ≤
        ((2 * nFaces2 1 + 2 : ℕ) : ℕ∞) ∧
      (branchTopFaces (n := n) (p := p) Pi2).encard ≤
        ((2 * nFaces2 (n + p - 2) + 3 : ℕ) : ℕ∞)) := by
  rcases hsplit with ⟨s, rfl, rfl⟩
  have hLower :
      is_polyhedron (split_branch_lower P s s.π0) :=
    splitBranchLower_isPolyhedron hP s s.π0
  have hUpper :
      is_polyhedron (split_branch_upper P s s.π0) :=
    splitBranchUpper_isPolyhedron hP s s.π0
  have hIndexOne : 1 ≤ n + p - 2 := by omega
  have hLowerOne := hFaces1 1 (by omega) hIndexOne
  have hLowerCodimTwo := hFaces1 (n + p - 2) hIndexOne (by omega)
  have hUpperOne := hFaces2 1 (by omega) hIndexOne
  have hUpperCodimTwo := hFaces2 (n + p - 2) hIndexOne (by omega)
  -- Apply the endpoint and ridge bounds to each branch, then substitute the prescribed counts.
  constructor
  · constructor
    · simpa [branchZeroFaces, hLowerOne] using
        zeroDimensionalExposedFaces_encard_le_twice_oneDimensional hLower
    · simpa [branchTopFaces, hLowerCodimTwo] using
        ambientTopExposedFaces_encard_le_twice_codimTwo hLower hambient
  · constructor
    · simpa [branchZeroFaces, hUpperOne] using
        zeroDimensionalExposedFaces_encard_le_twice_oneDimensional hUpper
    · simpa [branchTopFaces, hUpperCodimTwo] using
        ambientTopExposedFaces_encard_le_twice_codimTwo hUpper hambient

/-- Helper for Exercise 5.2: restricting an exposed equality face along a subset is the equality
face of the restricted ambient set. -/
lemma inter_faceSet_eq_faceSet_of_subset
    {Pi Q : Set (Fin (n + p) → ℝ)}
    {c : Fin (n + p) → ℝ}
    {δ : ℝ}
    (hQPi : Q ⊆ Pi) :
    Q ∩ face_set Pi c δ = face_set Q c δ := by
  ext x
  rw [Set.mem_inter_iff, mem_face_set_iff, mem_face_set_iff]
  constructor
  · rintro ⟨hxQ, hxFace⟩
    exact ⟨hxQ, hxFace.2⟩
  · rintro ⟨hxQ, hxEq⟩
    exact ⟨hxQ, ⟨hQPi hxQ, hxEq⟩⟩

/-- Helper for Exercise 5.2: a valid inequality on `Pi` remains exposed after restriction to a
subset `Q ⊆ Pi`. -/
lemma isExposed_inter_faceSet_of_subset
    {Pi Q : Set (Fin (n + p) → ℝ)}
    {c : Fin (n + p) → ℝ}
    {δ : ℝ}
    (hQPi : Q ⊆ Pi)
    (hvalid : is_valid_inequality Pi c δ) :
    IsExposed ℝ Q (Q ∩ face_set Pi c δ) := by
  rw [inter_faceSet_eq_faceSet_of_subset hQPi]
  exact isExposed_face_set_of_valid_inequality (P := Q) (c := c) (δ := δ) fun x hxQ ↦
    hvalid (hQPi hxQ)

/-- Helper for Exercise 5.2: a split-pair hull therefore has a numerical facet count. -/
lemma splitPair_has_facet_count
    {P Pi1 Pi2 : Set (Fin (n + p) → ℝ)}
    (hP : is_polyhedron P)
    (hsplit : exercise_5_2_is_split_pair (n := n) (p := p) P Pi1 Pi2) :
    ∃ nFacets : ℕ,
      exercise_5_2_has_facet_count (convexHull ℝ (Pi1 ∪ Pi2)) nFacets := by
  have hfiniteFacets :
      Set.Finite {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F} :=
    splitPair_finiteFacets (n := n) (p := p) hP hsplit
  -- Convert the finite facet family into the numeric count recorded by the helper predicate.
  refine ⟨hfiniteFacets.toFinset.card, ?_⟩
  exact hfiniteFacets.encard_eq_coe_toFinset_card

/-- Helper for Exercise 5.2: every facet of `conv(Π₁ ∪ Π₂)` is cut out by one supporting
equality, and that equality restricts to exposed branch traces whose convex hull recovers the
facet. -/
lemma facetAsConvexHullOfBranchFaceSets
    {Pi1 Pi2 F : Set (Fin (n + p) → ℝ)}
    (hFacet : IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F) :
    ∃ c : Fin (n + p) → ℝ, ∃ δ : ℝ,
      is_valid_inequality (convexHull ℝ (Pi1 ∪ Pi2)) c δ ∧
      F = face_set (convexHull ℝ (Pi1 ∪ Pi2)) c δ ∧
      IsExposed ℝ Pi1 (Pi1 ∩ F) ∧
      IsExposed ℝ Pi2 (Pi2 ∩ F) ∧
      Pi1 ∩ F = face_set Pi1 c δ ∧
      Pi2 ∩ F = face_set Pi2 c δ ∧
      F = convexHull ℝ ((Pi1 ∩ F) ∪ (Pi2 ∩ F)) := by
  let H : Set (Fin (n + p) → ℝ) := convexHull ℝ (Pi1 ∪ Pi2)
  rcases (isFacetOf_iff.mp hFacet) with ⟨hF_nonempty, hF_exposed, _⟩
  -- First rewrite the facet into the canonical equality-face owner of one valid inequality.
  rcases hF_exposed.exists_eq_face_set_of_nonempty hF_nonempty with ⟨c, δ, hvalid, hF_eq⟩
  have hPi1_subset : Pi1 ⊆ H := by
    intro x hx
    exact subset_convexHull ℝ (Pi1 ∪ Pi2) (Or.inl hx)
  have hPi2_subset : Pi2 ⊆ H := by
    intro x hx
    exact subset_convexHull ℝ (Pi1 ∪ Pi2) (Or.inr hx)
  have hPi1_exposed : IsExposed ℝ Pi1 (Pi1 ∩ F) := by
    -- Restrict the supporting equality face from the hull back to the first branch.
    rw [hF_eq]
    exact isExposed_inter_faceSet_of_subset hPi1_subset hvalid
  have hPi2_exposed : IsExposed ℝ Pi2 (Pi2 ∩ F) := by
    -- The same supporting equality cuts out the second branch trace as an exposed face.
    rw [hF_eq]
    exact isExposed_inter_faceSet_of_subset hPi2_subset hvalid
  have hPi1_eq : Pi1 ∩ F = face_set Pi1 c δ := by
    -- The first branch trace is literally the restricted equality face.
    rw [hF_eq]
    exact inter_faceSet_eq_faceSet_of_subset hPi1_subset
  have hPi2_eq : Pi2 ∩ F = face_set Pi2 c δ := by
    -- The second branch trace has the same canonical face-set description.
    rw [hF_eq]
    exact inter_faceSet_eq_faceSet_of_subset hPi2_subset
  have hUnion_valid :
      Pi1 ∪ Pi2 ⊆ ((dotProductStrongDual c).toLinearMap) ⁻¹' Set.Iic δ := by
    intro x hx
    have hxH : x ∈ H := subset_convexHull ℝ (Pi1 ∪ Pi2) hx
    simpa [Set.mem_preimage, dotProductStrongDual_apply] using hvalid hxH
  have hFace_eq_hyperplane :
      face_set H c δ = H ∩ ((dotProductStrongDual c).toLinearMap) ⁻¹' ({δ} : Set ℝ) := by
    ext x
    simp [Set.mem_preimage, mem_face_set_iff, dotProductStrongDual_apply]
  have hTrace_slice :
      (Pi1 ∪ Pi2) ∩ ((dotProductStrongDual c).toLinearMap) ⁻¹' ({δ} : Set ℝ) =
        (Pi1 ∩ F) ∪ (Pi2 ∩ F) := by
    ext x
    constructor
    · rintro ⟨hxUnion, hxHyper⟩
      rcases hxUnion with hxPi1 | hxPi2
      · left
        refine ⟨hxPi1, ?_⟩
        rw [hF_eq, hFace_eq_hyperplane]
        exact ⟨hPi1_subset hxPi1, hxHyper⟩
      · right
        refine ⟨hxPi2, ?_⟩
        rw [hF_eq, hFace_eq_hyperplane]
        exact ⟨hPi2_subset hxPi2, hxHyper⟩
    · rintro (⟨hxPi1, hxF⟩ | ⟨hxPi2, hxF⟩)
      · refine ⟨Or.inl hxPi1, ?_⟩
        rw [hF_eq, hFace_eq_hyperplane] at hxF
        exact hxF.2
      · refine ⟨Or.inr hxPi2, ?_⟩
        rw [hF_eq, hFace_eq_hyperplane] at hxF
        exact hxF.2
  have hFacet_convexHull :
      F = convexHull ℝ ((Pi1 ∩ F) ∪ (Pi2 ∩ F)) := by
    -- Intersect the hull with its supporting hyperplane and rewrite the boundary slice by traces.
    calc
      F = H ∩ ((dotProductStrongDual c).toLinearMap) ⁻¹' ({δ} : Set ℝ) := by
            rw [hF_eq, hFace_eq_hyperplane]
      _ = convexHull ℝ
            ((Pi1 ∪ Pi2) ∩ ((dotProductStrongDual c).toLinearMap) ⁻¹' ({δ} : Set ℝ)) := by
            simpa [H] using
              convexHull_inter_hyperplane_eq
                (Pi1 ∪ Pi2) ((dotProductStrongDual c).toLinearMap) δ hUnion_valid
      _ = convexHull ℝ ((Pi1 ∩ F) ∪ (Pi2 ∩ F)) := by
            rw [hTrace_slice]
  exact ⟨c, δ, hvalid, hF_eq, hPi1_exposed, hPi2_exposed, hPi1_eq, hPi2_eq, hFacet_convexHull⟩

/-- Helper for Exercise 5.2: the branch-trace pair attached to a candidate hull facet `F`. -/
def facetTracePair
    (Pi1 Pi2 : Set (Fin (n + p) → ℝ))
    (F : Set (Fin (n + p) → ℝ)) :
    Set (Fin (n + p) → ℝ) × Set (Fin (n + p) → ℝ) :=
  (Pi1 ∩ F, Pi2 ∩ F)

/-- Helper for Exercise 5.2: every branch trace lies in one of the counting buckets needed for the
final combinatorial estimate. -/
lemma polyhedronDim_countingBucket
    (F : Set (Fin (n + p) → ℝ)) :
    F = ∅ ∨
      polyhedronDim F = 0 ∨
      (1 ≤ polyhedronDim F ∧ polyhedronDim F ≤ n + p - 2) ∨
      n + p - 1 ≤ polyhedronDim F := by
  -- First separate the empty and zero-dimensional cases, then bucket the positive dimension by
  -- whether it lies inside or above the source-counted range.
  by_cases hEmpty : F = ∅
  · exact Or.inl hEmpty
  · right
    by_cases hZero : polyhedronDim F = 0
    · exact Or.inl hZero
    · have hPos : 1 ≤ polyhedronDim F := by
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hZero)
      by_cases hRange : polyhedronDim F ≤ n + p - 2
      · exact Or.inr (Or.inl ⟨hPos, hRange⟩)
      · exact Or.inr (Or.inr (by omega))

/-- Helper for Exercise 5.2: every actual facet trace pair lands in the explicit dimension buckets
used by the remaining counting argument. -/
lemma facetTraceDimensionAudit
    {Pi1 Pi2 F : Set (Fin (n + p) → ℝ)}
    (_hFacet : IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F) :
    (Pi1 ∩ F = ∅ ∨
        polyhedronDim (Pi1 ∩ F) = 0 ∨
        (1 ≤ polyhedronDim (Pi1 ∩ F) ∧ polyhedronDim (Pi1 ∩ F) ≤ n + p - 2) ∨
        n + p - 1 ≤ polyhedronDim (Pi1 ∩ F)) ∧
      (Pi2 ∩ F = ∅ ∨
        polyhedronDim (Pi2 ∩ F) = 0 ∨
        (1 ≤ polyhedronDim (Pi2 ∩ F) ∧ polyhedronDim (Pi2 ∩ F) ≤ n + p - 2) ∨
        n + p - 1 ≤ polyhedronDim (Pi2 ∩ F)) := by
  -- Once the trace pair has been fixed, the audit is a pure `polyhedronDim` bucket split on each
  -- branch component separately.
  exact ⟨polyhedronDim_countingBucket (n := n) (p := p) (Pi1 ∩ F),
    polyhedronDim_countingBucket (n := n) (p := p) (Pi2 ∩ F)⟩

/-- Helper for Exercise 5.2: a hull facet is recovered from its two branch traces, so the trace
map is injective on the facet family. -/
lemma facetTracePair_injective
    {Pi1 Pi2 : Set (Fin (n + p) → ℝ)} :
    Set.InjOn
      (facetTracePair (n := n) (p := p) Pi1 Pi2)
      {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F} := by
  intro F hF G hG hFG
  rcases facetAsConvexHullOfBranchFaceSets hF with
    ⟨cF, δF, _hvalidF, _hF_eq, _hF1_exposed, _hF2_exposed, _hF1_eq, _hF2_eq, hF_conv⟩
  rcases facetAsConvexHullOfBranchFaceSets hG with
    ⟨cG, δG, _hvalidG, _hG_eq, _hG1_exposed, _hG2_exposed, _hG1_eq, _hG2_eq, hG_conv⟩
  have hLeft : Pi1 ∩ F = Pi1 ∩ G := by
    simpa [facetTracePair] using congrArg Prod.fst hFG
  have hRight : Pi2 ∩ F = Pi2 ∩ G := by
    simpa [facetTracePair] using congrArg Prod.snd hFG
  -- Reconstruct both facets from their trace pairs and compare the resulting convex hulls.
  calc
    F = convexHull ℝ ((Pi1 ∩ F) ∪ (Pi2 ∩ F)) := hF_conv
    _ = convexHull ℝ ((Pi1 ∩ G) ∪ (Pi2 ∩ G)) := by rw [hLeft, hRight]
    _ = G := hG_conv.symm

/-- Helper for Exercise 5.2: every facet trace pair consists of exposed faces on the two split
branches. -/
lemma facetTracePairImage_subset_exposedPairs
    {Pi1 Pi2 : Set (Fin (n + p) → ℝ)} :
    facetTracePair (n := n) (p := p) Pi1 Pi2 ''
        {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F} ⊆
      {T : Set (Fin (n + p) → ℝ) × Set (Fin (n + p) → ℝ) |
        IsExposed ℝ Pi1 T.1 ∧ IsExposed ℝ Pi2 T.2} := by
  rintro T ⟨F, hF, rfl⟩
  rcases facetAsConvexHullOfBranchFaceSets hF with
    ⟨c, δ, _hvalid, _hF_eq, hF1_exposed, hF2_exposed, _hF1_eq, _hF2_eq, _hF_conv⟩
  -- The geometric reduction already packages both components of the trace pair as exposed faces.
  simpa [facetTracePair] using And.intro hF1_exposed hF2_exposed

/-- Helper for Exercise 5.2: every facet trace pair lies in the explicit dimension buckets needed
for the remaining branch-face counting step. -/
lemma facetTracePairImage_subset_auditedPairs
    {Pi1 Pi2 : Set (Fin (n + p) → ℝ)} :
    facetTracePair (n := n) (p := p) Pi1 Pi2 ''
        {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F} ⊆
      {T : Set (Fin (n + p) → ℝ) × Set (Fin (n + p) → ℝ) |
        (T.1 = ∅ ∨
            polyhedronDim T.1 = 0 ∨
            (1 ≤ polyhedronDim T.1 ∧ polyhedronDim T.1 ≤ n + p - 2) ∨
            n + p - 1 ≤ polyhedronDim T.1) ∧
          (T.2 = ∅ ∨
            polyhedronDim T.2 = 0 ∨
            (1 ≤ polyhedronDim T.2 ∧ polyhedronDim T.2 ≤ n + p - 2) ∨
            n + p - 1 ≤ polyhedronDim T.2)} := by
  rintro T ⟨F, hF, rfl⟩
  -- The audited trace buckets are exactly the two componentwise `polyhedronDim` splits above.
  simpa [facetTracePair] using
    facetTraceDimensionAudit (n := n) (p := p) (Pi1 := Pi1) (Pi2 := Pi2) (F := F) hF

/-- Helper for Exercise 5.2: the facet-trace image is finite because the hull facet family is
finite for every split pair of a polyhedron. -/
lemma facetTracePairImage_finite
    {P Pi1 Pi2 : Set (Fin (n + p) → ℝ)}
    (hP : is_polyhedron P)
    (hsplit : exercise_5_2_is_split_pair (n := n) (p := p) P Pi1 Pi2) :
    Set.Finite
      (facetTracePair (n := n) (p := p) Pi1 Pi2 ''
        {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F}) := by
  have hfiniteFacets :
      Set.Finite {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F} :=
    splitPair_finiteFacets (n := n) (p := p) hP hsplit
  -- The trace set is just the direct image of the finite hull-facet family.
  exact hfiniteFacets.image (facetTracePair (n := n) (p := p) Pi1 Pi2)

/-- Helper for Exercise 5.2: a family of pairs bounded componentwise by two face families has
cardinality at most the product of their cardinality budgets. -/
lemma encard_le_productBudget_of_subset
    {α β : Type*}
    {U : Set (α × β)}
    {S : Set α}
    {T : Set β}
    {a b : ℕ}
    (hU : U ⊆ S ×ˢ T)
    (hS : S.encard ≤ (a : ℕ∞))
    (hT : T.encard ≤ (b : ℕ∞)) :
    U.encard ≤ ((a * b : ℕ) : ℕ∞) := by
  -- First enlarge to the componentwise product, then multiply the two supplied bounds.
  calc
    U.encard ≤ (S ×ˢ T).encard := Set.encard_mono hU
    _ = S.encard * T.encard := Set.encard_prod
    _ ≤ (a : ℕ∞) * (b : ℕ∞) := mul_le_mul hS hT (by simp) (by simp)
    _ = ((a * b : ℕ) : ℕ∞) := by rw [ENat.coe_mul]

/-- Helper for Exercise 5.2: exposed faces transport through affine equivalences of
finite-dimensional real spaces. -/
private lemma isExposed_image_affineEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ᵃ[ℝ] F)
    {A B : Set E}
    (hAB : IsExposed ℝ A B) :
    IsExposed ℝ (e '' A) (e '' B) := by
  intro hB
  rcases hB with ⟨z, x, hxB, rfl⟩
  obtain ⟨l, hl⟩ := hAB ⟨x, hxB⟩
  let L : StrongDual ℝ F :=
    l.comp e.linear.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hcompare (u v : E) : L (e u) ≤ L (e v) ↔ l u ≤ l v := by
    -- Affine translations cancel when the two functional values are compared.
    have hdiff : L (e u) - L (e v) = l u - l v := by
      calc
        L (e u) - L (e v) = L (e u - e v) := by rw [map_sub]
        _ = l (e.linear.symm (e u - e v)) := rfl
        _ = l (u - v) := by
          have hediff : e u - e v = e.linear (u - v) := by
            symm
            exact e.toAffineMap.linearMap_vsub u v
          rw [hediff]
          simp
        _ = l u - l v := by rw [map_sub]
    constructor <;> intro h <;> linarith
  refine ⟨L, ?_⟩
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [hl] at hu
    refine ⟨⟨u, hu.1, rfl⟩, ?_⟩
    rintro _ ⟨v, hvA, rfl⟩
    exact (hcompare v u).2 (hu.2 v hvA)
  · rintro ⟨⟨u, huA, huy⟩, hymax⟩
    subst y
    refine ⟨u, ?_, rfl⟩
    rw [hl]
    refine ⟨huA, ?_⟩
    intro v hvA
    exact (hcompare v u).1 (hymax (e v) ⟨v, hvA, rfl⟩)

/-- Helper for Exercise 5.2: affine equivalences preserve affine-span direction dimension. -/
private lemma finrank_affineSpan_image_affineEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ᵃ[ℝ] F)
    (S : Set E) :
    Module.finrank ℝ (affineSpan ℝ (e '' S)).direction =
      Module.finrank ℝ (affineSpan ℝ S).direction := by
  have hmap : affineSpan ℝ (e '' S) = (affineSpan ℝ S).map e.toAffineMap := by
    -- Push the affine span through the same equivalence used on the set.
    symm
    exact AffineSubspace.map_span e.toAffineMap S
  rw [hmap, AffineSubspace.map_direction]
  exact LinearEquiv.finrank_map_eq e.linear (affineSpan ℝ S).direction

/-- Helper for Exercise 5.2: a facet transports forward through an affine equivalence. -/
private lemma isFacetOf_image_affineEquiv_forward
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ᵃ[ℝ] F)
    {A B : Set E}
    (h : IsFacetOf A B) :
    IsFacetOf (e '' A) (e '' B) := by
  rcases h with ⟨hB, hE, hdim⟩
  refine ⟨hB.image e, isExposed_image_affineEquiv e hE, ?_⟩
  rw [finrank_affineSpan_image_affineEquiv e B,
    finrank_affineSpan_image_affineEquiv e A]
  exact hdim

/-- Helper for Exercise 5.2: facets transport in both directions through an affine equivalence. -/
private lemma isFacetOf_image_affineEquiv
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ᵃ[ℝ] F)
    {A B : Set E} :
    IsFacetOf A B ↔ IsFacetOf (e '' A) (e '' B) := by
  refine ⟨isFacetOf_image_affineEquiv_forward e, ?_⟩
  intro h
  have h' := isFacetOf_image_affineEquiv_forward e.symm h
  have hA : e.symm '' (e '' A) = A := by
    ext x
    simp
  have hB : e.symm '' (e '' B) = B := by
    ext x
    simp
  rw [hA, hB] at h'
  exact h'

/-- Helper for Exercise 5.2: affine equivalences inject the facet family into the facets of the
image. -/
private lemma facetCount_le_affineImage
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (e : E ≃ᵃ[ℝ] F)
    (A : Set E) :
    {B : Set E | IsFacetOf A B}.encard ≤
      {C : Set F | IsFacetOf (e '' A) C}.encard := by
  let mapFace : Set E → Set F := fun B ↦ e '' B
  have hmapFace_injective : Function.Injective mapFace := by
    intro B C hBC
    dsimp [mapFace] at hBC
    ext x
    constructor
    · intro hx
      have hex : e x ∈ e '' B := ⟨x, hx, rfl⟩
      rw [hBC] at hex
      simpa using hex
    · intro hx
      have hex : e x ∈ e '' C := ⟨x, hx, rfl⟩
      rw [← hBC] at hex
      simpa using hex
  have himage_subset :
      mapFace '' {B : Set E | IsFacetOf A B} ⊆
        {C : Set F | IsFacetOf (e '' A) C} := by
    rintro C ⟨B, hB, rfl⟩
    exact (isFacetOf_image_affineEquiv e).1 hB
  -- Count the injective image and then enlarge to the full image-facet family.
  calc
    {B : Set E | IsFacetOf A B}.encard =
        (mapFace '' {B : Set E | IsFacetOf A B}).encard := by
          exact (hmapFace_injective.injOn.encard_image).symm
    _ ≤ {C : Set F | IsFacetOf (e '' A) C}.encard := Set.encard_mono himage_subset

/-- Helper for Exercise 5.2: the scalar used to shrink the octahedron is nonzero. -/
private lemma realHalf_ne_zero : (1 / 2 : ℝ) ≠ 0 := by
  -- This keeps the inverse needed by the affine equivalence out of its definition body.
  norm_num

/-- Helper for Exercise 5.2: the unit corresponding to multiplication by `1 / 2`. -/
private noncomputable def realHalfUnit : ℝˣ :=
  Units.mk0 (1 / 2 : ℝ) realHalf_ne_zero

/-- Helper for Exercise 5.2: shrink by `1 / 2` and then translate by `a`. -/
private noncomputable def shiftedHalfAffineEquiv
    {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (a : E) : E ≃ᵃ[ℝ] E :=
  (AffineEquiv.homothetyUnitsMulHom (0 : E) realHalfUnit).trans
    (AffineEquiv.constVAdd ℝ E a)

/-- Helper for Exercise 5.2: the shifted half-scale equivalence has its expected point formula. -/
@[simp] private lemma shiftedHalfAffineEquiv_apply
    {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (a x : E) :
    shiftedHalfAffineEquiv a x = a + (1 / 2 : ℝ) • x := by
  -- Evaluate the homothety first and the translation second.
  simp [shiftedHalfAffineEquiv, realHalfUnit, AffineMap.homothety_apply]

/-- Helper for Exercise 5.2: the Cayley translation anchor has total coordinate sum `1 / 2`. -/
private noncomputable def cayleyAnchor (r : ℕ) [NeZero r] : Fin r → ℝ :=
  Pi.single 0 (1 / 2 : ℝ)

/-- Helper for Exercise 5.2: summing the Cayley anchor leaves exactly half a unit. -/
private lemma sum_cayleyAnchor (r : ℕ) [NeZero r] :
    ∑ i : Fin r, cayleyAnchor r i = (1 / 2 : ℝ) := by
  -- Only coordinate `0` of the anchor is nonzero.
  simp [cayleyAnchor]

/-- Helper for Exercise 5.2: the low-constraint precursor joining the two translated simplex
slices of the octahedron. -/
private noncomputable def cayleySplitPrecursor (r : ℕ) [NeZero r] : Set (Fin r → ℝ) :=
  {x |
    0 ≤ ∑ i : Fin r, x i ∧
      (∑ i : Fin r, x i) ≤ 1 ∧
      ∀ i : Fin r,
        (1 / 2 : ℝ) * (∑ j : Fin r, x j) - x i ≤
            (1 / 2 : ℝ) - cayleyAnchor r i ∧
          x i - (1 / 2 : ℝ) * (∑ j : Fin r, x j) ≤ cayleyAnchor r i}

/-- Helper for Exercise 5.2: the row carrying the lower inequality for coordinate `i`. -/
private def cayleyLowerRow (r : ℕ) (i : Fin r) : Fin (2 * r + 2) :=
  ⟨i, by omega⟩

/-- Helper for Exercise 5.2: the row carrying the upper inequality for coordinate `i`. -/
private def cayleyUpperRow (r : ℕ) (i : Fin r) : Fin (2 * r + 2) :=
  ⟨r + i, by omega⟩

/-- Helper for Exercise 5.2: the row imposing nonnegativity of the coordinate sum. -/
private def cayleySumLowerRow (r : ℕ) : Fin (2 * r + 2) :=
  ⟨2 * r, by omega⟩

/-- Helper for Exercise 5.2: the row imposing that the coordinate sum is at most one. -/
private def cayleySumUpperRow (r : ℕ) : Fin (2 * r + 2) :=
  ⟨2 * r + 1, by omega⟩

/-- Helper for Exercise 5.2: the `2r+2` matrix presenting the Cayley precursor. -/
private noncomputable def cayleyConstraintMatrix (r : ℕ) [NeZero r] :
    Matrix (Fin (2 * r + 2)) (Fin r) ℝ :=
  fun k ↦
    if hkLower : k.1 < r then
      (fun _ ↦ (1 / 2 : ℝ)) - Pi.single ⟨k.1, hkLower⟩ 1
    else if hkUpper : k.1 < 2 * r then
      Pi.single ⟨k.1 - r, by omega⟩ 1 - (fun _ ↦ (1 / 2 : ℝ))
    else if k.1 = 2 * r then
      -1
    else
      1

/-- Helper for Exercise 5.2: the right-hand side paired with `cayleyConstraintMatrix`. -/
private noncomputable def cayleyConstraintRhs (r : ℕ) [NeZero r] : Fin (2 * r + 2) → ℝ :=
  fun k ↦
    if hkLower : k.1 < r then
      (1 / 2 : ℝ) - cayleyAnchor r ⟨k.1, hkLower⟩
    else if hkUpper : k.1 < 2 * r then
      cayleyAnchor r ⟨k.1 - r, by omega⟩
    else if k.1 = 2 * r then
      0
    else
      1

/-- Helper for Exercise 5.2: evaluation of a lower coordinate row. -/
private lemma cayleyConstraintMatrix_lowerRow
    (r : ℕ) [NeZero r] (i : Fin r) (x : Fin r → ℝ) :
    (cayleyConstraintMatrix r *ᵥ x) (cayleyLowerRow r i) =
      (1 / 2 : ℝ) * (∑ j : Fin r, x j) - x i := by
  -- Expand just this row; the single-coordinate dot product supplies `x i`.
  simp only [cayleyConstraintMatrix, cayleyLowerRow, Matrix.mulVec, dotProduct,
    Fin.is_lt, ↓reduceDIte]
  simp_rw [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  simp [Pi.single_apply, ← Finset.mul_sum]

/-- Helper for Exercise 5.2: evaluation of an upper coordinate row. -/
private lemma cayleyConstraintMatrix_upperRow
    (r : ℕ) [NeZero r] (i : Fin r) (x : Fin r → ℝ) :
    (cayleyConstraintMatrix r *ᵥ x) (cayleyUpperRow r i) =
      x i - (1 / 2 : ℝ) * (∑ j : Fin r, x j) := by
  -- Expand the second coordinate block and normalize its shifted row index.
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hnotLower : ¬r + i.1 < r := by omega
  have hupper : r + i.1 < 2 * r := by omega
  simp only [cayleyConstraintMatrix, cayleyUpperRow, Matrix.mulVec, dotProduct,
    hnotLower, hupper, ↓reduceDIte]
  simp_rw [Pi.sub_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  have hindex : (⟨r + i.1 - r, by omega⟩ : Fin r) = i := by
    apply Fin.ext
    exact Nat.add_sub_cancel_left r i.1
  rw [hindex]
  simp [Pi.single_apply, ← Finset.mul_sum]

/-- Helper for Exercise 5.2: evaluation of the lower coordinate-sum row. -/
private lemma cayleyConstraintMatrix_sumLowerRow
    (r : ℕ) [NeZero r] (x : Fin r → ℝ) :
    (cayleyConstraintMatrix r *ᵥ x) (cayleySumLowerRow r) =
      -(∑ j : Fin r, x j) := by
  -- The penultimate row has coefficient `-1` in every coordinate.
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hnotLower : ¬2 * r < r := by omega
  simp [cayleyConstraintMatrix, cayleySumLowerRow, Matrix.mulVec, dotProduct,
    hnotLower, Finset.sum_neg_distrib]

/-- Helper for Exercise 5.2: evaluation of the upper coordinate-sum row. -/
private lemma cayleyConstraintMatrix_sumUpperRow
    (r : ℕ) [NeZero r] (x : Fin r → ℝ) :
    (cayleyConstraintMatrix r *ᵥ x) (cayleySumUpperRow r) =
      ∑ j : Fin r, x j := by
  -- The final row has coefficient `1` in every coordinate.
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hnotLower : ¬2 * r + 1 < r := by omega
  have hnotUpper : ¬2 * r + 1 < 2 * r := by omega
  simp [cayleyConstraintMatrix, cayleySumUpperRow, Matrix.mulVec, dotProduct,
    hnotLower, hnotUpper]

/-- Helper for Exercise 5.2: evaluation of the lower row right-hand side. -/
private lemma cayleyConstraintRhs_lowerRow
    (r : ℕ) [NeZero r] (i : Fin r) :
    cayleyConstraintRhs r (cayleyLowerRow r i) =
      (1 / 2 : ℝ) - cayleyAnchor r i := by
  simp [cayleyConstraintRhs, cayleyLowerRow]

/-- Helper for Exercise 5.2: evaluation of the upper row right-hand side. -/
private lemma cayleyConstraintRhs_upperRow
    (r : ℕ) [NeZero r] (i : Fin r) :
    cayleyConstraintRhs r (cayleyUpperRow r i) = cayleyAnchor r i := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hnotLower : ¬r + i.1 < r := by omega
  have hupper : r + i.1 < 2 * r := by omega
  simp [cayleyConstraintRhs, cayleyUpperRow, hnotLower, hupper]

/-- Helper for Exercise 5.2: evaluation of the lower sum-row right-hand side. -/
private lemma cayleyConstraintRhs_sumLowerRow
    (r : ℕ) [NeZero r] :
    cayleyConstraintRhs r (cayleySumLowerRow r) = 0 := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hnotLower : ¬2 * r < r := by omega
  simp [cayleyConstraintRhs, cayleySumLowerRow, hnotLower]

/-- Helper for Exercise 5.2: evaluation of the upper sum-row right-hand side. -/
private lemma cayleyConstraintRhs_sumUpperRow
    (r : ℕ) [NeZero r] :
    cayleyConstraintRhs r (cayleySumUpperRow r) = 1 := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hnotLower : ¬2 * r + 1 < r := by omega
  have hnotUpper : ¬2 * r + 1 < 2 * r := by omega
  simp [cayleyConstraintRhs, cayleySumUpperRow, hnotLower, hnotUpper]

/-- Helper for Exercise 5.2: the explicit matrix has exactly the Cayley precursor as its
polyhedron. -/
private lemma cayleySplitPrecursor_eq_polyhedron (r : ℕ) [NeZero r] :
    cayleySplitPrecursor r =
      polyhedron_le_set (cayleyConstraintMatrix r) (cayleyConstraintRhs r) := by
  ext x
  rw [mem_polyhedron_le_set_iff]
  constructor
  · intro hx k
    by_cases hkLower : k.1 < r
    · let i : Fin r := ⟨k.1, hkLower⟩
      have hk : k = cayleyLowerRow r i := by
        apply Fin.ext
        rfl
      rw [hk, cayleyConstraintMatrix_lowerRow, cayleyConstraintRhs_lowerRow]
      exact (hx.2.2 i).1
    · by_cases hkUpper : k.1 < 2 * r
      · let i : Fin r := ⟨k.1 - r, by omega⟩
        have hk : k = cayleyUpperRow r i := by
          apply Fin.ext
          dsimp [cayleyUpperRow, i]
          omega
        rw [hk, cayleyConstraintMatrix_upperRow, cayleyConstraintRhs_upperRow]
        exact (hx.2.2 i).2
      · by_cases hkSum : k.1 = 2 * r
        · have hk : k = cayleySumLowerRow r := by
            apply Fin.ext
            simpa [cayleySumLowerRow]
          rw [hk, cayleyConstraintMatrix_sumLowerRow, cayleyConstraintRhs_sumLowerRow]
          linarith [hx.1]
        · have hk : k = cayleySumUpperRow r := by
            apply Fin.ext
            dsimp [cayleySumUpperRow]
            omega
          rw [hk, cayleyConstraintMatrix_sumUpperRow, cayleyConstraintRhs_sumUpperRow]
          exact hx.2.1
  · intro hx
    have hsumLower := hx (cayleySumLowerRow r)
    have hsumUpper := hx (cayleySumUpperRow r)
    rw [cayleyConstraintMatrix_sumLowerRow] at hsumLower
    rw [cayleyConstraintMatrix_sumUpperRow] at hsumUpper
    rw [cayleyConstraintRhs_sumLowerRow] at hsumLower
    rw [cayleyConstraintRhs_sumUpperRow] at hsumUpper
    refine ⟨by linarith, hsumUpper, ?_⟩
    intro i
    have hlower := hx (cayleyLowerRow r i)
    have hupper := hx (cayleyUpperRow r i)
    rw [cayleyConstraintMatrix_lowerRow] at hlower
    rw [cayleyConstraintMatrix_upperRow] at hupper
    rw [cayleyConstraintRhs_lowerRow] at hlower
    rw [cayleyConstraintRhs_upperRow] at hupper
    exact ⟨hlower, hupper⟩

/-- Helper for Exercise 5.2: the selector split sums all Cayley coordinates. -/
private def cayleySplitCoeffs (r : ℕ) : Fin r → ℤ :=
  fun _ ↦ 1

/-- Helper for Exercise 5.2: the all-ones selector vector is nonzero in positive dimension. -/
private lemma cayleySplitCoeffs_ne_zero (r : ℕ) [NeZero r] :
    cayleySplitCoeffs r ≠ 0 := by
  -- Coordinate `0` distinguishes the selector from the zero vector.
  intro hzero
  have hcoord := congrFun hzero (0 : Fin r)
  simp [cayleySplitCoeffs] at hcoord

/-- Helper for Exercise 5.2: the all-ones selector is supported on the full coordinate set. -/
private lemma cayleySplitCoeffs_zero_on_compl (r : ℕ) :
    ∀ j ∈ (Finset.univ : Finset (Fin r))ᶜ, cayleySplitCoeffs r j = 0 := by
  -- The complement of the full coordinate set is empty.
  intro j hj
  simp at hj

/-- Helper for Exercise 5.2: the genuine split selecting the two endpoint simplex slices. -/
private def cayleySelectorSplit (r : ℕ) [NeZero r] :
    Split (Finset.univ : Finset (Fin r)) :=
  ⟨cayleySplitCoeffs r, 0, cayleySplitCoeffs_ne_zero r,
    cayleySplitCoeffs_zero_on_compl r⟩

/-- Helper for Exercise 5.2: the selector split value is the ordinary coordinate sum. -/
private lemma cayleySelectorSplit_dot (r : ℕ) [NeZero r] (x : Fin r → ℝ) :
    split_dot (cayleySelectorSplit r) x = ∑ i : Fin r, x i := by
  -- Every integral selector coefficient is `1`.
  simp [split_dot_eq_sum, cayleySelectorSplit, cayleySplitCoeffs]

/-- Helper for Exercise 5.2: every simplex coordinate is at most its total mass `1`. -/
private lemma stdSimplex_coord_le_one {r : ℕ} {z : Fin r → ℝ}
    (hz : z ∈ stdSimplex ℝ (Fin r)) (i : Fin r) : z i ≤ 1 := by
  -- Compare one nonnegative summand with the simplex's normalized coordinate sum.
  rw [← hz.2]
  exact Finset.single_le_sum (fun j _ ↦ hz.1 j) (Finset.mem_univ i)

/-- Helper for Exercise 5.2: the lower selector branch is the translated negative simplex. -/
private lemma cayleySplitPrecursor_lowerBranch {r : ℕ} [NeZero r] :
    split_branch_lower (cayleySplitPrecursor r) (cayleySelectorSplit r)
        (cayleySelectorSplit r).π0 =
      shiftedHalfAffineEquiv (cayleyAnchor r) ''
        ((fun z : Fin r → ℝ ↦ -z) '' stdSimplex ℝ (Fin r)) := by
  ext y
  constructor
  · intro hy
    rw [mem_split_branch_lower_iff, cayleySelectorSplit_dot] at hy
    have hsumUpper : ∑ i : Fin r, y i ≤ 0 := by
      simpa [cayleySelectorSplit] using hy.2
    have hsum : ∑ i : Fin r, y i = 0 := le_antisymm hsumUpper hy.1.1
    let z : Fin r → ℝ := fun i ↦ 2 * (cayleyAnchor r i - y i)
    have hz_nonneg : ∀ i, 0 ≤ z i := by
      intro i
      have hi := (hy.1.2.2 i).2
      rw [hsum] at hi
      dsimp [z]
      linarith
    have hz_sum : ∑ i : Fin r, z i = 1 := by
      calc
        ∑ i : Fin r, z i = 2 * ∑ i : Fin r, (cayleyAnchor r i - y i) := by
          simp only [z]
          rw [Finset.mul_sum]
        _ = 2 * ((∑ i : Fin r, cayleyAnchor r i) - ∑ i : Fin r, y i) := by
          rw [Finset.sum_sub_distrib]
        _ = 1 := by rw [sum_cayleyAnchor, hsum]; norm_num
    have hz : z ∈ stdSimplex ℝ (Fin r) := ⟨hz_nonneg, hz_sum⟩
    -- The precursor inequalities reconstruct the negative simplex coordinatewise.
    refine ⟨-z, ⟨z, hz, rfl⟩, ?_⟩
    ext i
    rw [shiftedHalfAffineEquiv_apply]
    simp [z]
  · rintro ⟨w, ⟨z, hz, rfl⟩, rfl⟩
    rw [mem_split_branch_lower_iff, cayleySelectorSplit_dot]
    have hsum : ∑ i : Fin r,
        shiftedHalfAffineEquiv (cayleyAnchor r) (-z) i = 0 := by
      simp_rw [shiftedHalfAffineEquiv_apply, Pi.add_apply, Pi.smul_apply,
        Pi.neg_apply]
      simp_rw [smul_eq_mul]
      rw [Finset.sum_add_distrib, sum_cayleyAnchor, ← Finset.mul_sum,
        Finset.sum_neg_distrib, hz.2]
      norm_num
    refine ⟨?_, ?_⟩
    · refine ⟨by rw [hsum], ?_⟩
      refine ⟨by rw [hsum]; norm_num, ?_⟩
      intro i
      constructor
      · have hzi := stdSimplex_coord_le_one hz i
        rw [hsum, shiftedHalfAffineEquiv_apply]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
        dsimp
        linarith
      · have hzi := hz.1 i
        rw [hsum, shiftedHalfAffineEquiv_apply]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply]
        dsimp
        linarith
    · simpa only [cayleySelectorSplit, Int.cast_zero] using hsum.le

/-- Helper for Exercise 5.2: the upper selector branch is the translated positive simplex. -/
private lemma cayleySplitPrecursor_upperBranch {r : ℕ} [NeZero r] :
    split_branch_upper (cayleySplitPrecursor r) (cayleySelectorSplit r)
        (cayleySelectorSplit r).π0 =
      shiftedHalfAffineEquiv (cayleyAnchor r) '' stdSimplex ℝ (Fin r) := by
  ext y
  constructor
  · intro hy
    rw [mem_split_branch_upper_iff, cayleySelectorSplit_dot] at hy
    have hsumLower : 1 ≤ ∑ i : Fin r, y i := by
      simpa [cayleySelectorSplit] using hy.2
    have hsum : ∑ i : Fin r, y i = 1 := le_antisymm hy.1.2.1 hsumLower
    let z : Fin r → ℝ := fun i ↦ 2 * (y i - cayleyAnchor r i)
    have hz_nonneg : ∀ i, 0 ≤ z i := by
      intro i
      have hi := (hy.1.2.2 i).1
      rw [hsum] at hi
      dsimp [z]
      linarith
    have hz_sum : ∑ i : Fin r, z i = 1 := by
      calc
        ∑ i : Fin r, z i = 2 * ∑ i : Fin r, (y i - cayleyAnchor r i) := by
          simp only [z]
          rw [Finset.mul_sum]
        _ = 2 * ((∑ i : Fin r, y i) - ∑ i : Fin r, cayleyAnchor r i) := by
          rw [Finset.sum_sub_distrib]
        _ = 1 := by rw [sum_cayleyAnchor, hsum]; norm_num
    have hz : z ∈ stdSimplex ℝ (Fin r) := ⟨hz_nonneg, hz_sum⟩
    -- The precursor inequalities reconstruct the positive simplex coordinatewise.
    refine ⟨z, hz, ?_⟩
    ext i
    rw [shiftedHalfAffineEquiv_apply]
    simp [z]
  · rintro ⟨z, hz, rfl⟩
    rw [mem_split_branch_upper_iff, cayleySelectorSplit_dot]
    have hsum : ∑ i : Fin r,
        shiftedHalfAffineEquiv (cayleyAnchor r) z i = 1 := by
      simp_rw [shiftedHalfAffineEquiv_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_add_distrib, sum_cayleyAnchor, ← Finset.mul_sum, hz.2]
      norm_num
    refine ⟨?_, ?_⟩
    · refine ⟨by rw [hsum]; norm_num, ?_⟩
      refine ⟨by rw [hsum], ?_⟩
      intro i
      constructor
      · have hzi := hz.1 i
        rw [hsum, shiftedHalfAffineEquiv_apply]
        simp only [Pi.add_apply, Pi.smul_apply]
        dsimp
        linarith
      · have hzi := stdSimplex_coord_le_one hz i
        rw [hsum, shiftedHalfAffineEquiv_apply]
        simp only [Pi.add_apply, Pi.smul_apply]
        dsimp
        linarith
    · simpa only [cayleySelectorSplit, Int.cast_zero, zero_add] using hsum.ge

/-- Helper for Exercise 5.2: joining the positive and negative simplices gives the octahedron. -/
private lemma convexHull_neg_stdSimplex_union_eq_octahedron {r : ℕ} (hr : 0 < r) :
    convexHull ℝ
        (((fun z : Fin r → ℝ ↦ -z) '' stdSimplex ℝ (Fin r)) ∪
          stdSimplex ℝ (Fin r)) =
      octahedron r := by
  let V : Set (Fin r → ℝ) := Set.range (fun i : Fin r ↦ Pi.single i (1 : ℝ))
  have hsimplex : convexHull ℝ V = stdSimplex ℝ (Fin r) := by
    exact convexHull_rangle_single_eq_stdSimplex ℝ (Fin r)
  have hneg :
      convexHull ℝ ((fun z : Fin r → ℝ ↦ -z) '' V) =
        (fun z : Fin r → ℝ ↦ -z) '' stdSimplex ℝ (Fin r) := by
    -- Transport the simplex hull through negation once, before joining the two sides.
    simpa only [← Set.image_neg_eq_neg, hsimplex] using (convexHull_neg (𝕜 := ℝ) V)
  calc
    convexHull ℝ
          (((fun z : Fin r → ℝ ↦ -z) '' stdSimplex ℝ (Fin r)) ∪
            stdSimplex ℝ (Fin r)) =
        convexHull ℝ
          (convexHull ℝ ((fun z : Fin r → ℝ ↦ -z) '' V) ∪ convexHull ℝ V) := by
            rw [hneg, hsimplex]
    _ = convexHull ℝ (((fun z : Fin r → ℝ ↦ -z) '' V) ∪ V) := by
          rw [convexHull_convexHull_union_left, convexHull_convexHull_union_right]
    _ = octahedron r := by
          rw [octahedron_eq_convexHull_vertices hr]
          congr 1
          ext x
          constructor
          · rintro (⟨y, ⟨i, rfl⟩, rfl⟩ | hxV)
            · exact Or.inr ⟨i, rfl⟩
            · exact Or.inl hxV
          · rintro (hxV | ⟨i, rfl⟩)
            · exact Or.inr hxV
            · exact Or.inl ⟨Pi.single i (1 : ℝ), ⟨i, rfl⟩, rfl⟩

/-- Helper for Exercise 5.2: the split-disjunctive hull is a shifted affine octahedron. -/
private lemma cayleySplitPrecursor_hull {r : ℕ} [NeZero r] :
    convexHull ℝ
        (split_branch_lower (cayleySplitPrecursor r) (cayleySelectorSplit r)
            (cayleySelectorSplit r).π0 ∪
          split_branch_upper (cayleySplitPrecursor r) (cayleySelectorSplit r)
            (cayleySelectorSplit r).π0) =
      shiftedHalfAffineEquiv (cayleyAnchor r) '' octahedron r := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  -- Rewrite both selector slices, merge their images, and commute affine image with convex hull.
  rw [cayleySplitPrecursor_lowerBranch, cayleySplitPrecursor_upperBranch,
    ← Set.image_union]
  calc
    convexHull ℝ
        (shiftedHalfAffineEquiv (cayleyAnchor r) ''
          (((fun z : Fin r → ℝ ↦ -z) '' stdSimplex ℝ (Fin r)) ∪
            stdSimplex ℝ (Fin r))) =
      shiftedHalfAffineEquiv (cayleyAnchor r) ''
        convexHull ℝ
          (((fun z : Fin r → ℝ ↦ -z) '' stdSimplex ℝ (Fin r)) ∪
            stdSimplex ℝ (Fin r)) :=
        (AffineMap.image_convexHull
          (shiftedHalfAffineEquiv (cayleyAnchor r)).toAffineMap _).symm
    _ = shiftedHalfAffineEquiv (cayleyAnchor r) '' octahedron r := by
          rw [convexHull_neg_stdSimplex_union_eq_octahedron hr]

/-- Helper for Exercise 5.2: different sign patterns cut out different signed facets of the
octahedron. -/
lemma octahedron_signedFace_injective {r : ℕ} :
    Function.Injective (fun S : Finset (Fin r) ↦ octahedron_signed_face r S) := by
  classical
  intro S T hST
  by_cases hEq : S = T
  · exact hEq
  have hdiff :
      ∃ i : Fin r, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
    by_contra hNoDiff
    apply hEq
    ext i
    constructor
    · intro hiS
      by_contra hiT
      exact hNoDiff ⟨i, Or.inl ⟨hiS, hiT⟩⟩
    · intro hiT
      by_contra hiS
      exact hNoDiff ⟨i, Or.inr ⟨hiT, hiS⟩⟩
  rcases hdiff with ⟨i, hiST | hiTS⟩
  · have hmemS :
        octahedron_signed_vertex S i ∈ octahedron_signed_face r S :=
      octahedron_signed_vertex_mem_face S i
    have hmemT :
        octahedron_signed_vertex S i ∈ octahedron_signed_face r T := by
      simpa [hST] using hmemS
    rw [mem_octahedron_signed_face_iff] at hmemT
    -- The sign-compatible vertex for `S` violates the `T`-face equality once `i` changes sign.
    have hsum :
        signed_coordinate_sum T (octahedron_signed_vertex S i) = -1 := by
      simp [octahedron_signed_vertex, signed_coordinate_sum, hiST.1, hiST.2]
    linarith [hmemT.2]
  · have hmemT :
        octahedron_signed_vertex T i ∈ octahedron_signed_face r T :=
      octahedron_signed_vertex_mem_face T i
    have hmemS :
        octahedron_signed_vertex T i ∈ octahedron_signed_face r S := by
      simpa [hST] using hmemT
    rw [mem_octahedron_signed_face_iff] at hmemS
    -- Swapping the roles of `S` and `T` gives the same separating witness.
    have hsum :
        signed_coordinate_sum S (octahedron_signed_vertex T i) = -1 := by
      simp [octahedron_signed_vertex, signed_coordinate_sum, hiTS.1, hiTS.2]
    linarith [hmemS.2]

/-- Helper for Exercise 5.2: the signed-facet family gives at least `2^r` facets of the
`r`-dimensional octahedron. -/
lemma octahedron_facetCount_lowerBound {r : ℕ} (hr : 0 < r) :
    ((2 ^ r : ℕ) : ℕ∞) ≤
      {F : Set (Fin r → ℝ) | IsFacetOf (octahedron r) F}.encard := by
  classical
  let signedFace : Finset (Fin r) → Set (Fin r → ℝ) := fun S ↦ octahedron_signed_face r S
  have hsignedFace_inj :
      Set.InjOn signedFace (Set.univ : Set (Finset (Fin r))) := by
    intro S _ T _ hEq
    exact octahedron_signedFace_injective hEq
  have hsignedFace_subset :
      signedFace '' (Set.univ : Set (Finset (Fin r))) ⊆
        {F : Set (Fin r → ℝ) | IsFacetOf (octahedron r) F} := by
    rintro F ⟨S, -, rfl⟩
    -- Every signed equality face is already a facet of the octahedron.
    exact octahedron_signed_face_isFacetOf hr S
  calc
    ((2 ^ r : ℕ) : ℕ∞) = (Set.univ : Set (Finset (Fin r))).encard := by
          simp
    _ = (signedFace '' (Set.univ : Set (Finset (Fin r)))).encard := by
          simpa [signedFace] using hsignedFace_inj.encard_image.symm
    _ ≤ {F : Set (Fin r → ℝ) | IsFacetOf (octahedron r) F}.encard :=
          Set.encard_mono hsignedFace_subset

/-- Helper for Exercise 5.2: the Cayley precursor's split hull inherits the exponential
octahedron facet lower bound. -/
private lemma cayleySplitPrecursor_facetCount_lowerBound {r : ℕ} [NeZero r] :
    ((2 ^ r : ℕ) : ℕ∞) ≤
      {F : Set (Fin r → ℝ) |
        IsFacetOf
          (convexHull ℝ
            (split_branch_lower (cayleySplitPrecursor r) (cayleySelectorSplit r)
                (cayleySelectorSplit r).π0 ∪
              split_branch_upper (cayleySplitPrecursor r) (cayleySelectorSplit r)
                (cayleySelectorSplit r).π0)) F}.encard := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  rw [cayleySplitPrecursor_hull]
  -- First use the signed octahedron facets, then inject them through the affine copy.
  exact (octahedron_facetCount_lowerBound hr).trans
    (facetCount_le_affineImage (shiftedHalfAffineEquiv (cayleyAnchor r)) (octahedron r))

/-- Helper for Exercise 5.2: the witness dimension extracts half of the available row budget,
while remaining positive for every row count. -/
private def cayleyFamilyDim (m : ℕ) : ℕ :=
  max 1 ((m - 2) / 2)

/-- Helper for Exercise 5.2: every member of the witness family has positive dimension. -/
private lemma cayleyFamilyDim_pos (m : ℕ) : 0 < cayleyFamilyDim m := by
  -- The outer maximum supplies a coordinate even for the small unused row counts.
  simp [cayleyFamilyDim]

/-- Helper for Exercise 5.2: the positive family dimension supplies the selector's nonzero
coordinate. -/
private instance cayleyFamilyDim_neZero (m : ℕ) : NeZero (cayleyFamilyDim m) :=
  ⟨Nat.ne_of_gt (cayleyFamilyDim_pos m)⟩

/-- Helper for Exercise 5.2: when the row count exactly fits the Cayley presentation, reuse its
matrix; otherwise use a harmless zero presentation. -/
private noncomputable def cayleyFamilyMatrix (m : ℕ) :
    Matrix (Fin m) (Fin (cayleyFamilyDim m)) ℝ :=
  if h : m = 2 * cayleyFamilyDim m + 2 then
    fun k ↦
      cayleyConstraintMatrix (cayleyFamilyDim m)
        (Fin.cast h k)
  else
    0

/-- Helper for Exercise 5.2: the family right-hand side matches the selected matrix branch. -/
private noncomputable def cayleyFamilyRhs (m : ℕ) : Fin m → ℝ :=
  if h : m = 2 * cayleyFamilyDim m + 2 then
    fun k ↦ cayleyConstraintRhs (cayleyFamilyDim m) (Fin.cast h k)
  else
    0

/-- Helper for Exercise 5.2: the precursor family is defined by its exact-row presentation. -/
private noncomputable def cayleyFamilyPolyhedron (m : ℕ) :
    Set (Fin (cayleyFamilyDim m) → ℝ) :=
  polyhedron_le_set (cayleyFamilyMatrix m) (cayleyFamilyRhs m)

/-- Helper for Exercise 5.2: the family always uses the genuine full-support selector split. -/
private def cayleyFamilySplit (m : ℕ) :
    Split (Finset.univ : Finset (Fin (cayleyFamilyDim m))) :=
  cayleySelectorSplit (cayleyFamilyDim m)

/-- Helper for Exercise 5.2: the lower family member is the actual lower selector branch. -/
private noncomputable def cayleyFamilyLower (m : ℕ) :
    Set (Fin (cayleyFamilyDim m) → ℝ) :=
  split_branch_lower (cayleyFamilyPolyhedron m) (cayleyFamilySplit m)
    (cayleyFamilySplit m).π0

/-- Helper for Exercise 5.2: the upper family member is the actual upper selector branch. -/
private noncomputable def cayleyFamilyUpper (m : ℕ) :
    Set (Fin (cayleyFamilyDim m) → ℝ) :=
  split_branch_upper (cayleyFamilyPolyhedron m) (cayleyFamilySplit m)
    (cayleyFamilySplit m).π0

/-- Helper for Exercise 5.2: at row count `2r+2`, the family dimension is exactly `r`. -/
private lemma cayleyFamilyDim_two_mul_add_two {r : ℕ} (hr : 0 < r) :
    cayleyFamilyDim (2 * r + 2) = r := by
  -- Subtraction and division undo the chosen even row count, and positivity removes the maximum.
  simp [cayleyFamilyDim, Nat.max_eq_right (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt hr))]

/-- Helper for Exercise 5.2: at a fitted row count the presented family member is the Cayley
precursor. -/
private lemma cayleyFamilyPolyhedron_two_mul_add_two {r : ℕ} (hr : 0 < r) :
    cayleyFamilyPolyhedron (2 * r + 2) =
      cayleySplitPrecursor (cayleyFamilyDim (2 * r + 2)) := by
  have hd : cayleyFamilyDim (2 * r + 2) = r := cayleyFamilyDim_two_mul_add_two hr
  have hrows : 2 * r + 2 = 2 * cayleyFamilyDim (2 * r + 2) + 2 := by
    rw [hd]
  -- Select the fitted matrix branch and discard the proof-only row cast.
  rw [cayleyFamilyPolyhedron, cayleyFamilyMatrix, cayleyFamilyRhs,
    dif_pos hrows, dif_pos hrows, cayleySplitPrecursor_eq_polyhedron]
  ext x
  rw [mem_polyhedron_le_set_iff, mem_polyhedron_le_set_iff]
  constructor
  · intro hx k
    simpa using hx (Fin.cast hrows.symm k)
  · intro hx k
    simpa using hx (Fin.cast hrows k)

/-- Helper for Exercise 5.2: every fitted family member retains the exponential facet lower
bound. -/
private lemma cayleyFamily_facetCount_lowerBound {r : ℕ} (hr : 0 < r) :
    ((2 ^ r : ℕ) : ℕ∞) ≤
      {F : Set (Fin (cayleyFamilyDim (2 * r + 2)) → ℝ) |
        IsFacetOf
          (convexHull ℝ
            (cayleyFamilyLower (2 * r + 2) ∪
              cayleyFamilyUpper (2 * r + 2))) F}.encard := by
  have hd : cayleyFamilyDim (2 * r + 2) = r := cayleyFamilyDim_two_mul_add_two hr
  -- Normalize the fitted family data to the already-counted precursor and selector.
  calc
    ((2 ^ r : ℕ) : ℕ∞) =
        ((2 ^ cayleyFamilyDim (2 * r + 2) : ℕ) : ℕ∞) := by rw [hd]
    _ ≤ {F : Set (Fin (cayleyFamilyDim (2 * r + 2)) → ℝ) |
          IsFacetOf
            (convexHull ℝ
              (cayleyFamilyLower (2 * r + 2) ∪
                cayleyFamilyUpper (2 * r + 2))) F}.encard := by
          rw [cayleyFamilyLower, cayleyFamilyUpper, cayleyFamilySplit,
            cayleyFamilyPolyhedron_two_mul_add_two hr]
          exact cayleySplitPrecursor_facetCount_lowerBound

/-- Helper for Exercise 5.2: from dimension four onward, the exponential bound dominates the
square bound used in the final growth estimate. -/
private lemma square_le_two_pow {r : ℕ} (hr : 4 ≤ r) : r * r ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      rw [pow_succ]
      nlinarith

/-- Exercise 5.2 (1). Let `P`, `Π₁`, and `Π₂` be as in `(5.1)`, so `Π₁` and `Π₂` are the two
split branches of `P`. If, for each `k = 1, …, n + p - 2`, the polyhedra `Π₁` and `Π₂` have
`n_k^1` and `n_k^2` `k`-dimensional faces, respectively, then, in the nondegenerate regime
`3 ≤ n + p`, there exists a combinatorial upper bound on the number of facets of
`conv(Π₁ ∪ Π₂)` depending only on these source face numbers. -/
theorem exercise_5_2_facet_bound_of_split_pair
    (hambient : 3 ≤ n + p) :
    ∃ B : (ℕ → ℕ) → (ℕ → ℕ) → ℕ,
      exercise_5_2_is_combinatorial_facet_bound n p B := by
  classical
  -- Route correction: the open step is now purely combinatorial. Every hull facet has already
  -- been reduced to a pair of exposed branch traces cut out by one supporting equality.
  refine ⟨fun nFaces1 nFaces2 ↦
    exercise_5_2_branchBudget n p nFaces1 * exercise_5_2_branchBudget n p nFaces2, ?_⟩
  intro P Pi1 Pi2 nFaces1 nFaces2 hP hsplit _hambient hFaces1 hFaces2
  let traceImage :
      Set (Set (Fin (n + p) → ℝ) × Set (Fin (n + p) → ℝ)) :=
    facetTracePair (n := n) (p := p) Pi1 Pi2 ''
      {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F}
  have htraceImage_finite : traceImage.Finite := by
    -- The trace-image reduction has now been separated from the later bucket counts.
    simpa [traceImage] using
      facetTracePairImage_finite (n := n) (p := p) (P := P) (Pi1 := Pi1) (Pi2 := Pi2) hP hsplit
  have hfacetEncard_eq_traceImage :
      {F : Set (Fin (n + p) → ℝ) | IsFacetOf (convexHull ℝ (Pi1 ∪ Pi2)) F}.encard =
        traceImage.encard := by
    -- The facet is reconstructed from its two branch traces, so counting facets reduces
    -- injectively to counting trace pairs.
    simpa [traceImage] using
      (facetTracePair_injective (n := n) (p := p) (Pi1 := Pi1) (Pi2 := Pi2)).encard_image.symm
  have htraceImage_exposed :
      traceImage ⊆
        {T : Set (Fin (n + p) → ℝ) × Set (Fin (n + p) → ℝ) |
          IsExposed ℝ Pi1 T.1 ∧ IsExposed ℝ Pi2 T.2} := by
    -- The geometric decomposition records exposedness for both components of every trace pair.
    simpa [traceImage] using
      facetTracePairImage_subset_exposedPairs (n := n) (p := p) (Pi1 := Pi1) (Pi2 := Pi2)
  have htraceImage_audit :
      traceImage ⊆
        {T : Set (Fin (n + p) → ℝ) × Set (Fin (n + p) → ℝ) |
          (T.1 = ∅ ∨
              polyhedronDim T.1 = 0 ∨
              (1 ≤ polyhedronDim T.1 ∧ polyhedronDim T.1 ≤ n + p - 2) ∨
              n + p - 1 ≤ polyhedronDim T.1) ∧
            (T.2 = ∅ ∨
              polyhedronDim T.2 = 0 ∨
              (1 ≤ polyhedronDim T.2 ∧ polyhedronDim T.2 ≤ n + p - 2) ∨
              n + p - 1 ≤ polyhedronDim T.2)} := by
    -- No trace pair is omitted from the later counting buckets: the residual top-dimensional case
    -- is now explicit instead of implicit.
    simpa [traceImage] using
      facetTracePairImage_subset_auditedPairs (n := n) (p := p) (Pi1 := Pi1) (Pi2 := Pi2)
  have htraceImage_subset :
      traceImage ⊆
        branchAuditedFaces (n := n) (p := p) Pi1 ×ˢ
          branchAuditedFaces (n := n) (p := p) Pi2 := by
    intro T hT
    have hExposed := htraceImage_exposed hT
    have hAudit := htraceImage_audit hT
    exact ⟨⟨hExposed.1, hAudit.1⟩, hExposed.2, hAudit.2⟩
  obtain ⟨⟨hzero1, htop1⟩, ⟨hzero2, htop2⟩⟩ :=
    splitPair_boundaryFaceCounts_le (n := n) (p := p) hP hsplit hambient hFaces1 hFaces2
  have hbranch1 :
      (branchAuditedFaces (n := n) (p := p) Pi1).encard ≤
        (exercise_5_2_branchBudget n p nFaces1 : ℕ∞) :=
    branchAuditedFaces_encard_le_branchBudget hFaces1 hzero1 htop1
  have hbranch2 :
      (branchAuditedFaces (n := n) (p := p) Pi2).encard ≤
        (exercise_5_2_branchBudget n p nFaces2 : ℕ∞) :=
    branchAuditedFaces_encard_le_branchBudget hFaces2 hzero2 htop2
  -- The two branch budgets multiply after the trace image is placed in their Cartesian product.
  rw [hfacetEncard_eq_traceImage]
  exact encard_le_productBudget_of_subset htraceImage_subset hbranch1 hbranch2

/-- Exercise 5.2 (2). One can construct a family of polyhedra `P` with `m` constraints whose
associated split-disjunctive hulls `conv(Π₁ ∪ Π₂)` have more than linear facet growth in `m`;
the ambient dimension and the designated mixed-integer coordinates are allowed to vary with `m`.
-/
theorem exists_polyhedron_family_with_superlinear_split_disjunctive_facet_growth :
    ∃ d : ℕ → ℕ, ∃ P : ∀ m : ℕ, Set (Fin (d m) → ℝ),
      ∃ I : ∀ m : ℕ, Finset (Fin (d m)),
        ∃ Pi1 Pi2 : ∀ m : ℕ, Set (Fin (d m) → ℝ),
        ∃ _hP : exercise_5_2_has_m_constraint_presentations d P,
          ∃ _hsplit : exercise_5_2_is_split_family d I P Pi1 Pi2,
            exercise_5_2_has_superlinear_split_disjunctive_facet_growth d Pi1 Pi2 := by
  classical
  -- Route correction: use the explicit selector-split Cayley family above; fitted row counts give
  -- affine octahedra, while all other row counts retain a tautological matrix presentation.
  refine ⟨cayleyFamilyDim, cayleyFamilyPolyhedron,
    fun m ↦ (Finset.univ : Finset (Fin (cayleyFamilyDim m))),
    cayleyFamilyLower, cayleyFamilyUpper, ?_, ?_, ?_⟩
  · intro m
    -- The family was defined directly from an `m`-row matrix and right-hand side.
    exact ⟨cayleyFamilyMatrix m, cayleyFamilyRhs m, rfl⟩
  · intro m
    -- Both displayed branches are, by definition, cut out by the same genuine selector split.
    exact ⟨cayleyFamilySplit m, rfl, rfl⟩
  · intro C
    let r : ℕ := 4 * (C + 1)
    let m : ℕ := 2 * r + 2
    refine ⟨m, ?_⟩
    have hr : 0 < r := by
      dsimp [r]
      omega
    have hr4 : 4 ≤ r := by
      dsimp [r]
      omega
    have hlinear_square : C * m < r * r := by
      dsimp [m, r]
      nlinarith
    have hlinear_pow : C * m < 2 ^ r :=
      hlinear_square.trans_le (square_le_two_pow hr4)
    have hcoe : ((C * m : ℕ) : ℕ∞) < ((2 ^ r : ℕ) : ℕ∞) := by
      exact_mod_cast hlinear_pow
    -- The fitted family member has at least `2^r` facets, which beats the chosen linear value.
    exact hcoe.trans_le (by
      simpa [m] using cayleyFamily_facetCount_lowerBound hr)

end Exercise52

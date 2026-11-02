import Mathlib.Order.Preorder.Finite
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_24

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this proposition:
-- * primary domain: exposed faces of Chapter 3 polyhedra in `ℝ^n`
-- * source-facing owner: `is_polyhedron`
-- * core/canonical owners: mathlib's `IsExposed` and the chapter owner `linealitySpace`
-- * exact canonical recall: Proposition 3.25 (3) is the `ℝ^n` specialization of
--   `IsExposed.inter`

section Proposition325

variable {n : ℕ} {P F F' G : Set (Fin n → ℝ)}

attribute [local instance] Classical.propDecidable

/-- Helper for Proposition 3.25: package an active-constraint face as a polyhedron by keeping the
original rows and then appending the opposite inequalities for the rows in `I`. -/
noncomputable def activeConstraintFaceMatrix
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) :
    Matrix (Fin (m + m)) (Fin n) ℝ :=
  Fin.append A (fun i' j ↦ if i' ∈ I then -A i' j else 0)

/-- Helper for Proposition 3.25: right-hand sides for the auxiliary polyhedron presenting
`active_constraint_face A b I`. -/
noncomputable def activeConstraintFaceRhs {m : ℕ} (b : Fin m → ℝ) (I : Set (Fin m)) :
    Fin (m + m) → ℝ :=
  Fin.append b (fun i' ↦ if i' ∈ I then -b i' else 0)

/-- Helper for Proposition 3.25: the first block of auxiliary rows is the original matrix. -/
lemma activeConstraintFaceMatrix_castAdd
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) (i : Fin m) :
    activeConstraintFaceMatrix A I (Fin.castAdd m i) = A i := by
  simp [activeConstraintFaceMatrix]

/-- Helper for Proposition 3.25: an appended auxiliary row indexed by `i ∈ I` is `-A i`. -/
lemma activeConstraintFaceMatrix_natAdd_of_mem
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) (i : Fin m) (hi : i ∈ I) :
    activeConstraintFaceMatrix A I (Fin.natAdd m i) = -A i := by
  ext j
  rw [activeConstraintFaceMatrix, Fin.append_right]
  simp [hi]

/-- Helper for Proposition 3.25: an appended auxiliary row indexed by `i ∉ I` is the zero row. -/
lemma activeConstraintFaceMatrix_natAdd_of_not_mem
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) (i : Fin m) (hi : i ∉ I) :
    activeConstraintFaceMatrix A I (Fin.natAdd m i) = 0 := by
  ext j
  rw [activeConstraintFaceMatrix, Fin.append_right]
  simp [hi]

/-- Helper for Proposition 3.25: an appended auxiliary row indexed by `i ∈ I` evaluates to the
negative of the original row under `mulVec`. -/
lemma activeConstraintFaceMatrix_mulVec_natAdd_of_mem
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) (x : Fin n → ℝ)
    (i : Fin m) (hi : i ∈ I) :
    (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) = -((A *ᵥ x) i) := by
  rw [Matrix.mulVec, activeConstraintFaceMatrix_natAdd_of_mem A I i hi]
  exact neg_dotProduct (A i) x

/-- Helper for Proposition 3.25: an appended auxiliary row indexed by `i ∉ I` evaluates to `0`
under `mulVec`. -/
lemma activeConstraintFaceMatrix_mulVec_natAdd_of_not_mem
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) (x : Fin n → ℝ)
    (i : Fin m) (hi : i ∉ I) :
    (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) = 0 := by
  rw [Matrix.mulVec, activeConstraintFaceMatrix_natAdd_of_not_mem A I i hi]
  simp

/-- Helper for Proposition 3.25: the first block of auxiliary right-hand sides is the original
vector `b`. -/
lemma activeConstraintFaceRhs_castAdd
    {m : ℕ} (b : Fin m → ℝ) (I : Set (Fin m)) (i : Fin m) :
    activeConstraintFaceRhs b I (Fin.castAdd m i) = b i := by
  simp [activeConstraintFaceRhs]

/-- Helper for Proposition 3.25: an appended auxiliary right-hand side indexed by `i ∈ I` is
`-b i`. -/
lemma activeConstraintFaceRhs_natAdd_of_mem
    {m : ℕ} (b : Fin m → ℝ) (I : Set (Fin m)) (i : Fin m) (hi : i ∈ I) :
    activeConstraintFaceRhs b I (Fin.natAdd m i) = -b i := by
  rw [activeConstraintFaceRhs, Fin.append_right]
  simp [hi]

/-- Helper for Proposition 3.25: an appended auxiliary right-hand side indexed by `i ∉ I` is `0`.
-/
lemma activeConstraintFaceRhs_natAdd_of_not_mem
    {m : ℕ} (b : Fin m → ℝ) (I : Set (Fin m)) (i : Fin m) (hi : i ∉ I) :
    activeConstraintFaceRhs b I (Fin.natAdd m i) = 0 := by
  rw [activeConstraintFaceRhs, Fin.append_right]
  simp [hi]

/-- Helper for Proposition 3.25: the auxiliary matrix system cuts out exactly the prescribed
active-constraint face. -/
lemma active_constraint_face_eq_polyhedronAux
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (I : Set (Fin m)) :
    active_constraint_face A b I =
      polyhedron_le_set (activeConstraintFaceMatrix A I) (activeConstraintFaceRhs b I) := by
  ext x
  constructor
  · intro hx
    change activeConstraintFaceMatrix A I *ᵥ x ≤ activeConstraintFaceRhs b I
    intro p
    refine Fin.addCases ?_ ?_ p
    · intro i
      by_cases hi : i ∈ I
      · simpa [activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
          le_of_eq ((mem_active_constraint_face_iff.mp hx).1 i hi)
      · simpa [activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
          (mem_active_constraint_face_iff.mp hx).2 i hi
    · intro i
      by_cases hi : i ∈ I
      · have hi_eq : (A *ᵥ x) i = b i := (mem_active_constraint_face_iff.mp hx).1 i hi
        rw [activeConstraintFaceRhs_natAdd_of_mem b I i hi]
        rw [Matrix.mulVec, activeConstraintFaceMatrix_natAdd_of_mem A I i hi]
        have hneg_eq : (-A i) ⬝ᵥ x = -b i := by
          simpa [Matrix.mulVec, hi_eq]
        exact le_of_eq hneg_eq
      · rw [activeConstraintFaceRhs_natAdd_of_not_mem b I i hi]
        rw [Matrix.mulVec, activeConstraintFaceMatrix_natAdd_of_not_mem A I i hi]
        simp
  · intro hx
    refine (mem_active_constraint_face_iff).2 ?_
    constructor
    · intro i hi
      have hfalse : (A *ᵥ x) i ≤ b i := by
        simpa [activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
          hx (Fin.castAdd m i)
      have htrue : b i ≤ (A *ᵥ x) i := by
        have htrue' := hx (Fin.natAdd m i)
        rw [activeConstraintFaceRhs_natAdd_of_mem b I i hi] at htrue'
        rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A I x i hi] at htrue'
        have hneg : -((A *ᵥ x) i) ≤ -b i := htrue'
        linarith
      linarith
    · intro i hi
      simpa [activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
        hx (Fin.castAdd m i)

/-- Helper for Proposition 3.25: the auxiliary matrix has the same kernel as the original matrix,
because the added rows are either duplicates with a minus sign or trivial zero rows. -/
lemma activeConstraintFaceMatrix_mulVec_eq_zero_iff
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (I : Set (Fin m)) (r : Fin n → ℝ) :
    activeConstraintFaceMatrix A I *ᵥ r = 0 ↔ A *ᵥ r = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrArg (fun v ↦ v (Fin.castAdd m i)) h
    simpa [activeConstraintFaceMatrix, Matrix.mulVec] using hi
  · intro h
    ext p
    refine Fin.addCases ?_ ?_ p
    · intro i
      simpa [activeConstraintFaceMatrix, Matrix.mulVec] using congrArg (fun v ↦ v i) h
    · intro i
      by_cases hi : i ∈ I
      · have hi_zero : (A *ᵥ r) i = 0 := by
          simpa using congrArg (fun v ↦ v i) h
        rw [Pi.zero_apply]
        rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A I r i hi]
        have hneg_zero : -((A *ᵥ r) i) = 0 := by
          simpa using congrArg (fun t : ℝ ↦ -t) hi_zero
        exact hneg_zero
      · rw [Pi.zero_apply]
        rw [activeConstraintFaceMatrix_mulVec_natAdd_of_not_mem A I r i hi]

/-- Helper for Proposition 3.25: the lineality space of a nonempty polyhedron is the kernel of its
defining matrix. -/
lemma polyhedron_linealitySpace_eq_kernel_set
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (h_nonempty : (polyhedron_le_set A b).Nonempty) :
    linealitySpace (polyhedron_le_set A b) = {r : Fin n → ℝ | A *ᵥ r = 0} := by
  ext r
  constructor
  · intro hr
    rw [mem_linealitySpace_iff] at hr
    obtain ⟨x₀, hx₀⟩ := h_nonempty
    ext i
    by_contra hri
    let a : ℝ := (b i - (A *ᵥ x₀) i + 1) / (A *ᵥ r) i
    have ha_mem : x₀ + a • r ∈ polyhedron_le_set A b := hr hx₀ a
    have ha_le : (A *ᵥ (x₀ + a • r)) i ≤ b i := ha_mem i
    have hmul :
        a * (A *ᵥ r) i =
          b i - (A *ᵥ x₀) i + 1 := by
      dsimp [a]
      exact div_mul_cancel₀ _ hri
    have ha_eq : (A *ᵥ (x₀ + a • r)) i = b i + 1 := by
      calc
        (A *ᵥ (x₀ + a • r)) i = (A *ᵥ x₀) i + a * (A *ᵥ r) i := by
          simp [a, Matrix.mulVec_add, Matrix.mulVec_smul]
        _ = (A *ᵥ x₀) i + (b i - (A *ᵥ x₀) i + 1) := by
          rw [hmul]
        _ = b i + 1 := by ring
    linarith
  · intro hr
    rw [mem_linealitySpace_iff]
    intro x hx a
    change A *ᵥ (x + a • r) ≤ b
    intro i
    have hri : (A *ᵥ r) i = 0 := by
      simpa using congrArg (fun v ↦ v i) hr
    simpa [Matrix.mulVec_add, Matrix.mulVec_smul, hri] using hx i

/-- Helper for Proposition 3.25: every point of the affine hull of a set already lying in one
hyperplane still satisfies that defining equation. -/
lemma affineSpan_subset_hyperplane_of_subset
    {n : ℕ} {S : Set (Fin n → ℝ)} {c : Fin n → ℝ} {δ : ℝ}
    (hS : S ⊆ {x : Fin n → ℝ | c ⬝ᵥ x = δ}) :
    (affineSpan ℝ S : Set (Fin n → ℝ)) ⊆ {x : Fin n → ℝ | c ⬝ᵥ x = δ} := by
  intro x hx
  refine affineSpan_induction (k := ℝ) (s := S) (p := fun y : Fin n → ℝ ↦ c ⬝ᵥ y = δ) hx ?_ ?_
  · intro y hy
    exact hS hy
  · intro a u v w hu hv hw
    calc
      c ⬝ᵥ (a • (u - v) + w) = a * (c ⬝ᵥ u - c ⬝ᵥ v) + c ⬝ᵥ w := by
        simp [dotProduct_add, dotProduct_sub, dotProduct_smul]
      _ = a * (δ - δ) + δ := by rw [hu, hv, hw]
      _ = δ := by ring

/-- Helper for Proposition 3.25: a face of an active-constraint face is again an ambient
active-constraint face, obtained by activating more of the original rows. -/
lemma exists_ambient_activeConstraintFace_of_face_of_activeConstraintFace
    {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ} {b : Fin m → ℝ} {I : Set (Fin m)}
    {G : Set (Fin n → ℝ)}
    (_hF_nonempty : (active_constraint_face A b I).Nonempty)
    (hG : IsExposed ℝ (active_constraint_face A b I) G)
    (hG_nonempty : G.Nonempty) :
    ∃ J : Set (Fin m), I ⊆ J ∧ G = active_constraint_face A b J := by
  let A' : Matrix (Fin (m + m)) (Fin n) ℝ := activeConstraintFaceMatrix A I
  let b' : Fin (m + m) → ℝ := activeConstraintFaceRhs b I
  have hG' : IsExposed ℝ (polyhedron_le_set A' b') G := by
    simpa [A', b', active_constraint_face_eq_polyhedronAux] using hG
  obtain ⟨K, hK⟩ := exists_eq_active_constraint_face_of_isExposed A' b' G hG' hG_nonempty
  let J : Set (Fin m) := I ∪ {i : Fin m | Fin.castAdd m i ∈ K}
  refine ⟨J, Set.subset_union_left, ?_⟩
  ext x
  rw [hK, mem_active_constraint_face_iff, mem_active_constraint_face_iff]
  constructor
  · rintro ⟨hEq, hLe⟩
    constructor
    · intro i hiJ
      rw [Set.mem_union] at hiJ
      rcases hiJ with hiI | hiK
      · have hfalse_le : (A *ᵥ x) i ≤ b i := by
          by_cases hKfalse : Fin.castAdd m i ∈ K
          · have hEq' := hEq (Fin.castAdd m i) hKfalse
            simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec]
              using le_of_eq hEq'
          · simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec]
              using hLe (Fin.castAdd m i) hKfalse
        have htrue_le : b i ≤ (A *ᵥ x) i := by
          by_cases hKtrue : Fin.natAdd m i ∈ K
          · have hEq' := hEq (Fin.natAdd m i) hKtrue
            have hEq'' :
                (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) =
                  activeConstraintFaceRhs b I (Fin.natAdd m i) := by
              simpa [A', b'] using hEq'
            have hneg_eq : -((A *ᵥ x) i) = -b i := by
              rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A I x i hiI] at hEq''
              rw [activeConstraintFaceRhs_natAdd_of_mem b I i hiI] at hEq''
              exact hEq''
            linarith
          · have hineq := hLe (Fin.natAdd m i) hKtrue
            have hineq' :
                (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) ≤
                  activeConstraintFaceRhs b I (Fin.natAdd m i) := by
              simpa [A', b'] using hineq
            have hneg_le : -((A *ᵥ x) i) ≤ -b i := by
              rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A I x i hiI] at hineq'
              rw [activeConstraintFaceRhs_natAdd_of_mem b I i hiI] at hineq'
              exact hineq'
            linarith
        linarith
      · have hEq' := hEq (Fin.castAdd m i) hiK
        simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec]
          using hEq'
    · intro i hiJ
      have hiI : i ∉ I := by
        intro hiI
        rw [Set.mem_union] at hiJ
        exact hiJ (Or.inl hiI)
      have hiK : Fin.castAdd m i ∉ K := by
        intro hiK
        rw [Set.mem_union] at hiJ
        exact hiJ (Or.inr hiK)
      simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
        hLe (Fin.castAdd m i) hiK
  · rintro ⟨hEq, hLe⟩
    constructor
    · rw [Fin.forall_fin_add]
      constructor
      · intro i hpK
        have hiJ : i ∈ J := by
          rw [Set.mem_union]
          exact Or.inr hpK
        simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
          hEq i hiJ
      · intro i hpK
        by_cases hiI : i ∈ I
        · have hiJ : i ∈ J := Set.mem_union_left _ hiI
          have hEq' : (A *ᵥ x) i = b i := hEq i hiJ
          have hneg_eq : -((A *ᵥ x) i) = -b i := by
            simpa using congrArg (fun t : ℝ ↦ -t) hEq'
          have haux_eq :
              (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) =
                activeConstraintFaceRhs b I (Fin.natAdd m i) := by
            rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A I x i hiI]
            rw [activeConstraintFaceRhs_natAdd_of_mem b I i hiI]
            exact hneg_eq
          simpa [A', b'] using haux_eq
        · have haux_eq :
              (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) =
                activeConstraintFaceRhs b I (Fin.natAdd m i) := by
            rw [activeConstraintFaceMatrix_mulVec_natAdd_of_not_mem A I x i hiI]
            rw [activeConstraintFaceRhs_natAdd_of_not_mem b I i hiI]
          simpa [A', b'] using haux_eq
    · rw [Fin.forall_fin_add]
      constructor
      · intro i hpK
        by_cases hiJ : i ∈ J
        · simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
            le_of_eq (hEq i hiJ)
        · simpa [A', b', activeConstraintFaceMatrix, activeConstraintFaceRhs, Matrix.mulVec] using
            hLe i hiJ
      · intro i hpK
        by_cases hiI : i ∈ I
        · have hiJ : i ∈ J := Set.mem_union_left _ hiI
          have hEq' : (A *ᵥ x) i = b i := hEq i hiJ
          have hneg_eq : -((A *ᵥ x) i) = -b i := by
            simpa using congrArg (fun t : ℝ ↦ -t) hEq'
          have haux_le :
              (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) ≤
                activeConstraintFaceRhs b I (Fin.natAdd m i) := by
            rw [activeConstraintFaceMatrix_mulVec_natAdd_of_mem A I x i hiI]
            rw [activeConstraintFaceRhs_natAdd_of_mem b I i hiI]
            exact le_of_eq hneg_eq
          simpa [A', b'] using haux_le
        · have haux_le :
              (activeConstraintFaceMatrix A I *ᵥ x) (Fin.natAdd m i) ≤
                activeConstraintFaceRhs b I (Fin.natAdd m i) := by
            rw [activeConstraintFaceMatrix_mulVec_natAdd_of_not_mem A I x i hiI]
            rw [activeConstraintFaceRhs_natAdd_of_not_mem b I i hiI]
          simpa [A', b'] using haux_le

/-- Part (1) of Proposition 3.25. A polyhedron has only finitely many faces, with faces expressed by
mathlib's canonical `IsExposed` predicate. -/
theorem polyhedron_finite_faces (hP : is_polyhedron P) :
    Set.Finite {H : Set (Fin n → ℝ) | IsExposed ℝ P H} := by
  classical
  rcases is_polyhedron_iff.mp hP with ⟨m, A, b, rfl⟩
  -- Every nonempty exposed face is one active-constraint face, and `∅` is the only extra case.
  refine
    ((Set.finite_range (fun I : Set (Fin m) ↦ active_constraint_face A b I)).insert ∅).subset ?_
  intro H hH
  by_cases hH_nonempty : H.Nonempty
  · obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b H hH hH_nonempty
    exact Set.mem_insert_of_mem _ ⟨I, hI.symm⟩
  · exact Set.mem_insert_iff.mpr <| Or.inl (Set.not_nonempty_iff_eq_empty.mp hH_nonempty)

/-- Part (2) of Proposition 3.25. Every nonempty face of a polyhedron has the same
lineality space as the polyhedron. -/
theorem linealitySpace_eq_of_nonempty_face
    (hP : is_polyhedron P) (hF : IsExposed ℝ P F) (hF_nonempty : F.Nonempty) :
    linealitySpace F = linealitySpace P := by
  rcases is_polyhedron_iff.mp hP with ⟨m, A, b, rfl⟩
  obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF hF_nonempty
  obtain ⟨x₀, hx₀⟩ := hF_nonempty
  have hP_nonempty : (polyhedron_le_set A b).Nonempty :=
    ⟨x₀, hF.subset hx₀⟩
  have hF_nonempty' :
      (polyhedron_le_set
        (activeConstraintFaceMatrix A I)
        (activeConstraintFaceRhs b I)).Nonempty := by
    refine ⟨x₀, ?_⟩
    simpa [active_constraint_face_eq_polyhedronAux, hI] using hx₀
  -- Normalize both lineality spaces to matrix kernels and compare those kernels directly.
  calc
    linealitySpace F
        = {r : Fin n → ℝ | activeConstraintFaceMatrix A I *ᵥ r = 0} := by
            rw [hI, active_constraint_face_eq_polyhedronAux]
            exact polyhedron_linealitySpace_eq_kernel_set _ _ hF_nonempty'
    _ = {r : Fin n → ℝ | A *ᵥ r = 0} := by
          ext r
          exact activeConstraintFaceMatrix_mulVec_eq_zero_iff A I r
    _ = linealitySpace (polyhedron_le_set A b) := by
          symm
          exact polyhedron_linealitySpace_eq_kernel_set A b hP_nonempty

/- Part (3) of Proposition 3.25. The intersection of two faces of a polyhedron
is again a face. This is the `ℝ^n` specialization of the canonical mathlib
theorem `IsExposed.inter`. -/
recall IsExposed.inter

/-- Part (4) of Proposition 3.25. Two faces of a polyhedron are contained in a
unique inclusion-minimal face containing their union. -/
theorem existsUnique_minimal_face_containing_union
    (hP : is_polyhedron P) (hF : IsExposed ℝ P F) (hF' : IsExposed ℝ P F') :
    ∃! H : Set (Fin n → ℝ),
      Minimal (fun K : Set (Fin n → ℝ) ↦ IsExposed ℝ P K ∧ F ∪ F' ⊆ K) H := by
  classical
  let S : Set (Set (Fin n → ℝ)) := {K : Set (Fin n → ℝ) | IsExposed ℝ P K ∧ F ∪ F' ⊆ K}
  have hS_finite : S.Finite := by
    -- The search space is finite because all exposed faces of a polyhedron form a finite family.
    exact (polyhedron_finite_faces hP).subset fun K hK ↦ hK.1
  have hP_mem : P ∈ S := by
    constructor
    · exact IsExposed.refl P
    · intro x hx
      rcases hx with hx | hx
      · exact hF.subset hx
      · exact hF'.subset hx
  obtain ⟨H, _, hHmin_raw⟩ := Set.Finite.exists_le_minimal hS_finite hP_mem
  have hHmin : Minimal (fun K : Set (Fin n → ℝ) ↦ IsExposed ℝ P K ∧ F ∪ F' ⊆ K) H := by
    simpa [S] using hHmin_raw
  refine ⟨H, hHmin, ?_⟩
  intro H' hH'
  have hInter_prop :
      IsExposed ℝ P (H ∩ H') ∧ F ∪ F' ⊆ H ∩ H' := by
    constructor
    · exact hHmin.prop.1.inter hH'.prop.1
    · intro x hx
      exact ⟨hHmin.prop.2 hx, hH'.prop.2 hx⟩
  have hEq : H ∩ H' = H := Minimal.eq_of_subset hHmin hInter_prop Set.inter_subset_left
  have hEq' : H ∩ H' = H' := Minimal.eq_of_subset hH' hInter_prop Set.inter_subset_right
  exact hEq'.symm.trans hEq

/-- Part (5) of Proposition 3.25. Two faces of a polyhedron are distinct
exactly when their affine hulls are distinct. -/
theorem face_ne_iff_affineSpan_ne
    (hP : is_polyhedron P) (hF : IsExposed ℝ P F) (hF' : IsExposed ℝ P F') :
    F ≠ F' ↔ affineSpan ℝ F ≠ affineSpan ℝ F' := by
  constructor
  · intro hFF'
    -- Route correction: separate distinct faces by one active row that is tight on one face and
    -- strict at a point of the other face, then transport that separation to affine spans.
    rcases is_polyhedron_iff.mp hP with ⟨m, A, b, rfl⟩
    by_cases hF_empty : F = ∅
    · have hF'_nonempty : F'.Nonempty := by
        by_contra hF'_empty
        exact hFF' (hF_empty.trans (Set.not_nonempty_iff_eq_empty.mp hF'_empty).symm)
      obtain ⟨x, hx⟩ := hF'_nonempty
      have hxF' : x ∈ affineSpan ℝ F' := subset_affineSpan ℝ _ hx
      intro hAff
      have hAff' : affineSpan ℝ F' = ⊥ := by
        simpa [hF_empty] using hAff.symm
      rw [hAff'] at hxF'
      simpa using hxF'
    · by_cases hF'_empty : F' = ∅
      · have hF_nonempty : F.Nonempty := by
          exact Set.nonempty_iff_ne_empty.mpr hF_empty
        obtain ⟨x, hx⟩ := hF_nonempty
        have hxF : x ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hx
        intro hAff
        have hAff' : affineSpan ℝ F = ⊥ := by
          simpa [hF'_empty] using hAff
        rw [hAff'] at hxF
        simpa using hxF
      · have hF_nonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF_empty
        have hF'_nonempty : F'.Nonempty := Set.nonempty_iff_ne_empty.mpr hF'_empty
        obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF hF_nonempty
        obtain ⟨J, hJ⟩ := exists_eq_active_constraint_face_of_isExposed A b F' hF' hF'_nonempty
        by_cases hsub : F ⊆ F'
        · obtain ⟨x, hxF', hxnotF⟩ := Set.not_subset.mp (fun h ↦ hFF' (Set.Subset.antisymm hsub h))
          have hxP : x ∈ polyhedron_le_set A b := hF'.subset hxF'
          have hxP' : A *ᵥ x ≤ b := hxP
          have hnot_all : ¬ ∀ j : Fin m, j ∈ I → (A *ᵥ x) j = b j := by
            intro hAll
            apply hxnotF
            rw [hI]
            exact (mem_active_constraint_face_iff).2 ⟨hAll, fun j hj ↦ hxP' j⟩
          push Not at hnot_all
          obtain ⟨j, hjI, hjneq⟩ := hnot_all
          have hjlt : (A *ᵥ x) j < b j := lt_of_le_of_ne (hxP' j) hjneq
          have hFaceHyper :
              F ⊆ {y : Fin n → ℝ | A j ⬝ᵥ y = b j} := by
            intro y hy
            have hyEq :
                (A *ᵥ y) j = b j := by
                  have hyFace : y ∈ active_constraint_face A b I := by
                    simpa [hI] using hy
                  exact (mem_active_constraint_face_iff.mp hyFace).1 j hjI
            simpa [Matrix.mulVec] using hyEq
          have hAffHyper :=
            affineSpan_subset_hyperplane_of_subset (S := F) (c := A j) (δ := b j) hFaceHyper
          have hxAffF' : x ∈ affineSpan ℝ F' := subset_affineSpan ℝ _ hxF'
          have hxNotAffF : x ∉ affineSpan ℝ F := by
            intro hxAffF
            have hxEq : A j ⬝ᵥ x = b j := hAffHyper hxAffF
            have : (A *ᵥ x) j = b j := by simpa [Matrix.mulVec] using hxEq
            exact hjneq this
          intro hAff
          rw [← hAff] at hxAffF'
          exact hxNotAffF hxAffF'
        · obtain ⟨x, hxF, hxnotF'⟩ := Set.not_subset.mp hsub
          have hxP : x ∈ polyhedron_le_set A b := hF.subset hxF
          have hxP' : A *ᵥ x ≤ b := hxP
          have hnot_all : ¬ ∀ j : Fin m, j ∈ J → (A *ᵥ x) j = b j := by
            intro hAll
            apply hxnotF'
            rw [hJ]
            exact (mem_active_constraint_face_iff).2 ⟨hAll, fun j hj ↦ hxP' j⟩
          push Not at hnot_all
          obtain ⟨j, hjJ, hjneq⟩ := hnot_all
          have hFaceHyper :
              F' ⊆ {y : Fin n → ℝ | A j ⬝ᵥ y = b j} := by
            intro y hy
            have hyEq :
                (A *ᵥ y) j = b j := by
                  have hyFace : y ∈ active_constraint_face A b J := by
                    simpa [hJ] using hy
                  exact (mem_active_constraint_face_iff.mp hyFace).1 j hjJ
            simpa [Matrix.mulVec] using hyEq
          have hAffHyper :=
            affineSpan_subset_hyperplane_of_subset (S := F') (c := A j) (δ := b j) hFaceHyper
          have hxAffF : x ∈ affineSpan ℝ F := subset_affineSpan ℝ _ hxF
          have hxNotAffF' : x ∉ affineSpan ℝ F' := by
            intro hxAffF'
            have hxEq : A j ⬝ᵥ x = b j := hAffHyper hxAffF'
            have : (A *ᵥ x) j = b j := by simpa [Matrix.mulVec] using hxEq
            exact hjneq this
          intro hAff
          rw [hAff] at hxAffF
          exact hxNotAffF' hxAffF
  · intro hAff hFF'
    exact hAff (congrArg (affineSpan ℝ) hFF')

/-- Part (6) of Proposition 3.25. If one face of a polyhedron is properly
contained in another, then its dimension is at least one smaller, measured by
the direction of the affine hull. -/
theorem finrank_direction_affineSpan_le_sub_one_of_ssubset
    (hP : is_polyhedron P) (hF : IsExposed ℝ P F) (hF' : IsExposed ℝ P F') (hFF' : F ⊂ F') :
    Module.finrank ℝ (affineSpan ℝ F).direction ≤
      Module.finrank ℝ (affineSpan ℝ F').direction - 1 := by
  by_cases hF_empty : F = ∅
  · rw [hF_empty]
    have hEmptySpan : affineSpan ℝ (∅ : Set (Fin n → ℝ)) = ⊥ := by
      exact (affineSpan_eq_bot (k := ℝ) (s := (∅ : Set (Fin n → ℝ)))).2 rfl
    rw [hEmptySpan, AffineSubspace.direction_bot]
    rw [finrank_bot]
    exact Nat.zero_le (Module.finrank ℝ (affineSpan ℝ F').direction - 1)
  · have hAff_le : affineSpan ℝ F ≤ affineSpan ℝ F' := affineSpan_mono ℝ hFF'.subset
    have hAff_ne : affineSpan ℝ F ≠ affineSpan ℝ F' :=
      (face_ne_iff_affineSpan_ne hP hF hF').1 hFF'.ne
    have hAff_lt : affineSpan ℝ F < affineSpan ℝ F' := lt_of_le_of_ne hAff_le hAff_ne
    have hF_nonempty : F.Nonempty := Set.nonempty_iff_ne_empty.mpr hF_empty
    have hAff_nonempty :
        ((affineSpan ℝ F : AffineSubspace ℝ (Fin n → ℝ)) : Set (Fin n → ℝ)).Nonempty := by
      rcases hF_nonempty with ⟨x, hx⟩
      exact ⟨x, subset_affineSpan ℝ F hx⟩
    -- Turn strict affine-span inclusion into strict direction inclusion, then compare finranks.
    have hDir_lt :
        (affineSpan ℝ F).direction < (affineSpan ℝ F').direction :=
      AffineSubspace.direction_lt_of_nonempty
        (k := ℝ)
        (V := Fin n → ℝ)
        (P := Fin n → ℝ)
        (s₁ := affineSpan ℝ F)
        (s₂ := affineSpan ℝ F')
        hAff_lt
        hAff_nonempty
    have hFinrank_lt :
        Module.finrank ℝ (affineSpan ℝ F).direction <
          Module.finrank ℝ (affineSpan ℝ F').direction :=
      Submodule.finrank_lt_finrank_of_lt (K := ℝ) (V := Fin n → ℝ) hDir_lt
    exact Nat.le_pred_of_lt hFinrank_lt

/-- Proposition 3.25. A subset of a face `F` of a polyhedron is a face of `F` exactly when it
is a face of the ambient polyhedron contained in `F`. -/
theorem isExposed_iff_isExposed_of_subset
    (hP : is_polyhedron P) (hF : IsExposed ℝ P F) :
    IsExposed ℝ F G ↔ IsExposed ℝ P G ∧ G ⊆ F := by
  constructor
  · intro hG
    constructor
    · by_cases hG_empty : G = ∅
      · simpa [hG_empty] using (isExposed_empty : IsExposed ℝ P ∅)
      · rcases is_polyhedron_iff.mp hP with ⟨m, A, b, rfl⟩
        have hG_nonempty : G.Nonempty := Set.nonempty_iff_ne_empty.mpr hG_empty
        have hF_nonempty : F.Nonempty := by
          obtain ⟨x, hx⟩ := hG_nonempty
          exact ⟨x, hG.subset hx⟩
        obtain ⟨I, hI⟩ := exists_eq_active_constraint_face_of_isExposed A b F hF hF_nonempty
        have hG' : IsExposed ℝ (active_constraint_face A b I) G := by
          simpa [hI] using hG
        obtain ⟨J, _, hJ⟩ :=
          exists_ambient_activeConstraintFace_of_face_of_activeConstraintFace
            (A := A) (b := b) (I := I) (G := G) (by simpa [hI] using hF_nonempty) hG' hG_nonempty
        simpa [hJ] using active_constraint_face_isExposed A b J
    · exact hG.subset
  · rintro ⟨hG, hGF⟩
    exact hG.mono hF.subset hGF

end Proposition325

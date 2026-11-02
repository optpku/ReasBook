module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_definition_2_9
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_proposition_2_9
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_proposition_2_10
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_proposition_2_8.DoubleBlocker

public section

namespace SetTransversal

open scoped SetCoveringNotation

/-- Helper for Proposition 2.11: the characteristic vector has value one precisely on its
underlying finite set and value zero elsewhere. -/
private theorem characteristicVector_apply
    {n : ℕ} (U : Finset (Fin n)) (e : Fin n) :
    χ_{U} e = if e ∈ U then 1 else 0 := by
  have hTransversal :
      Clutter.IsTransversal Finset.univ
        ((∅ : Finset (Finset (Fin n))) : Set (Finset (Fin n))) U := by
    refine Clutter.IsTransversal.ofSubsetGroundAndHits (Finset.subset_univ U) ?_
    intro t ht
    simp at ht
  have hBinary : ∀ a, χ_{U} a = 0 ∨ χ_{U} a = 1 :=
    (mem_setCoveringFamily_incidenceMatrix_iff.mp
      (characteristicVector_mem_setCoveringFamily_of_transversal
        (T := (∅ : Finset (Finset (Fin n)))) hTransversal)).1
  have hSupport : χ_{U} e ≠ 0 ↔ e ∈ U := by
    -- The public support theorem supplies the pointwise behavior of the opaque imported vector.
    change e ∈ Function.support (χ_{U}) ↔ e ∈ U
    rw [support_characteristicVector]
    rfl
  by_cases he : e ∈ U
  · rcases hBinary e with hZero | hOne
    · exact False.elim (hSupport.mpr he hZero)
    · simp [he, hOne]
  · rcases hBinary e with hZero | hOne
    · simp [he, hZero]
    · have hNonzero : χ_{U} e ≠ 0 := by
        simp [hOne]
      exact False.elim (he (hSupport.mp hNonzero))

/-- The covering objective of the characteristic vector `χ_{U}` matches the minimum-weight set
objective of `U`. -/
theorem vectorObjective_characteristicVector_eq
    {n : ℕ} (w : Fin n → NNReal) (U : Finset (Fin n)) :
    SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) =
      (MinimumWeightSet.objective w U : ℝ) := by
  -- Expanding both objectives leaves exactly the weighted sum over the support `U`.
  simp [SetFamilyOptimization.objective_def, MinimumWeightSet.objective_def,
    characteristicVector_apply, Finset.sum_ite_mem]

/-- Helper for Proposition 2.11: the vector objective of a binary vector is the set objective
of its finite support. -/
private theorem vectorObjective_supportFilter_eq_of_binary
    {n : ℕ} (w : Fin n → NNReal) {x : Fin n → ℤ}
    (hx01 : ∀ e, x e = 0 ∨ x e = 1) :
    SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) x =
      (MinimumWeightSet.objective w
        (Finset.univ.filter fun e ↦ x e ≠ 0) : ℝ) := by
  -- Replace the binary vector by the characteristic vector of its support, then use the bridge.
  have hSupportRepresentation :
      x = χ_{Finset.univ.filter fun e ↦ x e ≠ 0} :=
    eq_characteristicVector_supportFilter_of_binary hx01
  calc
    SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) x =
        SetFamilyOptimization.objective (fun i ↦ (w i : ℝ))
          (χ_{Finset.univ.filter fun e ↦ x e ≠ 0}) :=
      congrArg (SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)))
        hSupportRepresentation
    _ = (MinimumWeightSet.objective w
          (Finset.univ.filter fun e ↦ x e ≠ 0) : ℝ) :=
      vectorObjective_characteristicVector_eq w _

/-- Any feasible covering vector yields a feasible characteristic vector of an inclusion-minimal
member of `R` with no larger objective value. -/
theorem exists_minimalMemberCover_le_of_mem
    {n : ℕ} (w : Fin n → NNReal)
    {R : Set (Finset (Fin n))} {S T : Finset (Finset (Fin n))}
    (hS_min : ∀ U : Finset (Fin n), U ∈ S ↔ U ∈ R ∧ Minimal (· ∈ R) U)
    (hST : IsBlockingPair S T)
    {x : Fin n → ℤ} (hx : x ∈ S^C(incidenceMatrix T)) :
    ∃ U : Finset (Fin n),
      U ∈ R ∧
      Minimal (· ∈ R) U ∧
      χ_{U} ∈ S^C(incidenceMatrix T) ∧
      SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) ≤
        SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) x := by
  rcases mem_setCoveringFamily_incidenceMatrix_iff.mp hx with ⟨hx01, hxHits⟩
  let support : Finset (Fin n) := Finset.univ.filter fun e ↦ x e ≠ 0
  have hSupportTransversal :
      Clutter.IsTransversal Finset.univ (T : Set (Finset (Fin n))) support := by
    -- Feasibility says exactly that the support of `x` meets every member of `T`.
    exact supportFilter_isTransversal_of_hits hxHits
  obtain ⟨U, hUBlocker, hUSubset⟩ :=
    Clutter.exists_blocker_subset_of_transversal Finset.univ
      (T : Set (Finset (Fin n))) hSupportTransversal
  have hBlocker :
      Clutter.blocker Finset.univ (T : Set (Finset (Fin n))) =
        (S : Set (Finset (Fin n))) := by
    -- The double-blocker theorem reverses the blocking-pair identity `T = blocker S`.
    calc
      Clutter.blocker Finset.univ (T : Set (Finset (Fin n))) =
          Clutter.blocker Finset.univ
            (Clutter.blocker Finset.univ (S : Set (Finset (Fin n)))) := by
        rw [hST.blocker_eq]
      _ = (S : Set (Finset (Fin n))) := by
        simpa using
          Clutter.blocker_blocker_eq Finset.univ
            (S : Set (Finset (Fin n))) hST.left_isClutter.toIsClutterOn
  have hUS : U ∈ S := by
    simpa only [hBlocker] using hUBlocker
  have hURMin : U ∈ R ∧ Minimal (· ∈ R) U := (hS_min U).mp hUS
  have hUCover : χ_{U} ∈ S^C(incidenceMatrix T) := by
    -- A blocker member is itself a transversal, hence its characteristic vector is feasible.
    exact characteristicVector_mem_setCoveringFamily_of_transversal
      (Clutter.mem_blocker_iff.mp hUBlocker).prop
  refine ⟨U, hURMin.1, hURMin.2, hUCover, ?_⟩
  have hObjectiveSupport :
      MinimumWeightSet.objective w U ≤ MinimumWeightSet.objective w support :=
    (MinimumWeightSet.objective_mono w) hUSubset
  -- Monotonicity on the extracted subset gives the desired comparison after both bridges.
  calc
    SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) =
        (MinimumWeightSet.objective w U : ℝ) :=
      vectorObjective_characteristicVector_eq w U
    _ ≤ (MinimumWeightSet.objective w support : ℝ) := by
      exact_mod_cast hObjectiveSupport
    _ = SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) x := by
      exact (vectorObjective_supportFilter_eq_of_binary w hx01).symm

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_4/ch2_sec2_4_3_proposition_2_11.lean.
Proposition 2.11 (1). The minimum-weight set problem over `R` and the covering problem on
`S^C(incidenceMatrix T)` have a common optimal characteristic vector coming from an
inclusion-minimal member of `R`, together with its covering feasibility and the equality of the
set and vector objectives. -/
theorem exists_commonOptimalPair
    {n : ℕ} (w : Fin n → NNReal)
    {R : Set (Finset (Fin n))} {S T : Finset (Finset (Fin n))}
    (hR : R.Nonempty)
    (hS_min : ∀ U : Finset (Fin n), U ∈ S ↔ U ∈ R ∧ Minimal (· ∈ R) U)
    (hST : IsBlockingPair S T) :
    ∃ U : Finset (Fin n),
      ∃ _hOptimal : MinimumWeightSet.IsOptimal w R U,
        ∃ _hU_min : Minimal (· ∈ R) U,
          ∃ _hU_cover : χ_{U} ∈ S^C(incidenceMatrix T),
            ∃ _hObjective :
              SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) =
                (MinimumWeightSet.objective w U : ℝ),
              ∀ y ∈ S^C(incidenceMatrix T),
                SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) ≤
                  SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) y := by
  obtain ⟨U, hOptimal, hU_min⟩ :=
    MinimumWeightSet.exists_isOptimal_minimalMember w hR
  have hUS : U ∈ S := (hS_min U).mpr ⟨hOptimal.mem, hU_min⟩
  have hU_cover : χ_{U} ∈ S^C(incidenceMatrix T) := by
    -- Proposition 2.9 identifies members of `S` with minimal feasible characteristic vectors.
    have hMinimalSupport :
        IsMinimalSupportMember (S^C(incidenceMatrix T)) (χ_{U}) :=
      (isMinimalSupportMember_setCoveringFamily_incidenceMatrix_iff hST).mpr
        ⟨U, hUS, rfl⟩
    exact (isMinimalSupportMember_iff.mp hMinimalSupport).1
  refine ⟨U, hOptimal, hU_min, hU_cover,
    vectorObjective_characteristicVector_eq w U, ?_⟩
  intro y hy
  obtain ⟨V, hVR, _, hV_cover, hV_le_y⟩ :=
    exists_minimalMemberCover_le_of_mem w hS_min hST hy
  have hUV : MinimumWeightSet.objective w U ≤ MinimumWeightSet.objective w V :=
    hOptimal.objective_le hVR
  -- Compare through the extracted minimal member `V`, which is no more expensive than `y`.
  calc
    SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) =
        (MinimumWeightSet.objective w U : ℝ) :=
      vectorObjective_characteristicVector_eq w U
    _ ≤ (MinimumWeightSet.objective w V : ℝ) := by
      exact_mod_cast hUV
    _ = SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{V}) := by
      exact (vectorObjective_characteristicVector_eq w V).symm
    _ ≤ SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) y := hV_le_y

/-- Proposition 2.11 (2). From any feasible set `F ∈ R`, one can obtain an optimal feasible
covering vector in `S^C(incidenceMatrix T)` without increasing the objective value. -/
theorem exists_optimalCover_le_of_mem
    {n : ℕ} (w : Fin n → NNReal)
    {R : Set (Finset (Fin n))} {S T : Finset (Finset (Fin n))}
    (hS_min : ∀ U : Finset (Fin n), U ∈ S ↔ U ∈ R ∧ Minimal (· ∈ R) U)
    (hST : IsBlockingPair S T)
    {F : Finset (Fin n)} (hF : F ∈ R) :
    ∃ y : Fin n → ℤ,
      ∃ _hy : y ∈ S^C(incidenceMatrix T),
        ∃ _hy_opt :
          ∀ z ∈ S^C(incidenceMatrix T),
            SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) y ≤
              SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) z,
          SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) y ≤
            (MinimumWeightSet.objective w F : ℝ) := by
  have hR : R.Nonempty := ⟨F, hF⟩
  obtain ⟨U, hOptimal, _, hU_cover, hObjective, hCoverOptimal⟩ :=
    exists_commonOptimalPair w hR hS_min hST
  refine ⟨χ_{U}, hU_cover, hCoverOptimal, ?_⟩
  have hUF : MinimumWeightSet.objective w U ≤ MinimumWeightSet.objective w F :=
    hOptimal.objective_le hF
  -- The common objective is bounded by the objective of the given feasible set `F`.
  calc
    SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) =
        (MinimumWeightSet.objective w U : ℝ) := hObjective
    _ ≤ (MinimumWeightSet.objective w F : ℝ) := by
      exact_mod_cast hUF

/-- Proposition 2.11 (3). From any feasible covering vector in `S^C(incidenceMatrix T)`, one can
obtain an optimal solution of the minimum-weight set problem over `R` without increasing the
objective value. -/
theorem exists_isOptimal_le_of_cover
    {n : ℕ} (w : Fin n → NNReal)
    {R : Set (Finset (Fin n))} {S T : Finset (Finset (Fin n))}
    (hR : R.Nonempty)
    (hS_min : ∀ U : Finset (Fin n), U ∈ S ↔ U ∈ R ∧ Minimal (· ∈ R) U)
    (hST : IsBlockingPair S T)
    {x : Fin n → ℤ} (hx : x ∈ S^C(incidenceMatrix T)) :
    ∃ U : Finset (Fin n),
      MinimumWeightSet.IsOptimal w R U ∧
      (MinimumWeightSet.objective w U : ℝ) ≤
        SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) x := by
  obtain ⟨U, hOptimal, _, _, hObjective, hCoverOptimal⟩ :=
    exists_commonOptimalPair w hR hS_min hST
  refine ⟨U, hOptimal, ?_⟩
  -- Evaluate cover optimality at the supplied feasible vector and rewrite the common objective.
  calc
    (MinimumWeightSet.objective w U : ℝ) =
        SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) (χ_{U}) := hObjective.symm
    _ ≤ SetFamilyOptimization.objective (fun i ↦ (w i : ℝ)) x :=
      hCoverOptimal x hx

end SetTransversal

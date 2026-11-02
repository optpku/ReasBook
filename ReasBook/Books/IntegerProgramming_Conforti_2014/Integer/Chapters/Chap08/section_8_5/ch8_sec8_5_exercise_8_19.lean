import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap08.section_8_5.ch8_sec8_5_exercise_8_18.FeasibilityCone

open scoped BigOperators Matrix

-- Domain sampling note:
-- * core/canonical Chapter 8 Benders owners: `benders_residual`,
--   `benders_subproblem_feasible_set`, `benders_feasibility_cone`
-- * core/canonical Chapter 3 ray owner: `IsExtremeRayOfCone`
-- * bridge/view finite-family owner reused from Exercise 8.18:
--   `IsExtremeRayRepresentativeFamily`
-- * core/canonical mathlib finite-index owners: `Fintype.card_pi`, `Fintype.card_sigma`
-- * source-facing owner kept here: the separable Exercise 8.19 Benders reformulation
-- This file therefore keeps only the separable layer and reuses the upstream Benders/extreme-ray
-- API instead of restating it locally.

section Exercise819

variable {s n m : ℕ}
variable {rowDim colDim : Fin s → ℕ}

/-- Helper for Exercise 8.19: every member of an
extreme-point representative family is an extreme point. -/
theorem IsExtremePointRepresentativeFamily.isExtremePoint
    {P : Set (Fin m → ℝ)}
    {q : ℕ}
    {points : Fin q → Fin m → ℝ}
    (hpoints : IsExtremePointRepresentativeFamily P points)
    (k : Fin q) :
    points k ∈ P.extremePoints ℝ := by
  -- Project the pointwise extreme-point condition from the canonical family predicate.
  exact hpoints.1 k

/-- Helper for Exercise 8.19: distinct indices in an
extreme-point representative family denote distinct points. -/
theorem IsExtremePointRepresentativeFamily.ne
    {P : Set (Fin m → ℝ)}
    {q : ℕ}
    {points : Fin q → Fin m → ℝ}
    (hpoints : IsExtremePointRepresentativeFamily P points)
    {k l : Fin q}
    (hkl : k ≠ l) :
    points k ≠ points l := by
  -- Project pairwise distinctness and specialize it to the two indices.
  exact hpoints.2.1 hkl

/-- Helper for Exercise 8.19: every extreme point is
listed by an extreme-point representative family. -/
theorem IsExtremePointRepresentativeFamily.exists_eq
    {P : Set (Fin m → ℝ)}
    {q : ℕ}
    {points : Fin q → Fin m → ℝ}
    (hpoints : IsExtremePointRepresentativeFamily P points)
    {x : Fin m → ℝ}
    (hx : x ∈ P.extremePoints ℝ) :
    ∃ k : Fin q, x = points k := by
  -- Project the spanning condition and apply it to the given extreme point.
  exact hpoints.2.2 x hx

/-- The blockwise dual polyhedron
`Q_i = {u^i ≥ 0 | u^i G_i ≥ h^i}` attached to the `i`-th subproblem of (8.32). -/
def separable_benders_dual_polyhedron
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ)
    (i : Fin s) : Set (Fin (rowDim i) → ℝ) :=
  {u | 0 ≤ u ∧ h i ≤ u ᵥ* G i}

/-- Membership in `separable_benders_dual_polyhedron G h i` is exactly the conjunction `u^i ≥ 0`
and `u^i G_i ≥ h^i`. -/
theorem mem_separable_benders_dual_polyhedron_iff
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ)
    (i : Fin s)
    (u : Fin (rowDim i) → ℝ) :
    u ∈ separable_benders_dual_polyhedron G h i ↔ 0 ≤ u ∧ h i ≤ u ᵥ* G i :=
  Iff.rfl

/-- The feasible set of the separable mixed problem (8.32), where the slave variables are the
dependent family `y^i` indexed by the blocks `i`. -/
def separable_benders_original_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ)) :
    Set ((Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ)) :=
  {xy |
    xy.1 ∈ X ∧
      ∀ i : Fin s,
        xy.2 i ∈ benders_subproblem_feasible_set (G i) (benders_residual (A i) (b i) xy.1)}

/-- Membership in `separable_benders_original_feasible_set A G b X` means `x ∈ X` and each block
component `y^i` solves the ordinary Benders subproblem with right-hand side `b^i - A_i x`. -/
theorem mem_separable_benders_original_feasible_set_iff
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ)) :
    xy ∈ separable_benders_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        ∀ i : Fin s,
          xy.2 i ∈ benders_subproblem_feasible_set (G i) (benders_residual (A i) (b i) xy.1) :=
  Iff.rfl

/-- The separable original feasible set consists of a global master restriction `x ∈ X` together
with blockwise membership in the ordinary Chapter 8 Benders feasible sets. -/
theorem mem_separable_benders_original_feasible_set_iff_forall_mem_benders_original_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (xy : (Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ)) :
    xy ∈ separable_benders_original_feasible_set A G b X ↔
      xy.1 ∈ X ∧
        ∀ i : Fin s,
          (xy.1, xy.2 i) ∈ benders_original_feasible_set (A i) (G i) (b i) Set.univ := by
  rw [mem_separable_benders_original_feasible_set_iff]
  constructor
  · intro hxy
    refine ⟨hxy.1, ?_⟩
    intro i
    rw [mem_benders_original_feasible_set_iff]
    exact ⟨Set.mem_univ _, hxy.2 i⟩
  · intro hxy
    refine ⟨hxy.1, ?_⟩
    intro i
    have hi :=
      (mem_benders_original_feasible_set_iff (A i) (G i) (b i) Set.univ (xy.1, xy.2 i)).1
        (hxy.2 i)
    exact hi.2

/-- The value `z_I` of the separable mixed problem (8.32), namely the maximum of
`c x + ∑_i h^i y^i` over the blockwise feasible pairs `(x, y)`. -/
noncomputable def separable_benders_original_value
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ) : ℝ :=
  sSup
    ((fun xy : (Fin n → ℝ) × (∀ i : Fin s, Fin (colDim i) → ℝ) ↦
        c ⬝ᵥ xy.1 + ∑ i : Fin s, h i ⬝ᵥ xy.2 i) ''
      separable_benders_original_feasible_set A G b X)

/-- The feasible set of the reformulation from Exercise 8.19(i), with one scalar `η_i` for each
block and with optimality and feasibility cuts indexed by the extreme points and extreme rays of
the corresponding block dual systems. -/
def separable_benders_master_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ) :
    Set ((Fin n → ℝ) × (Fin s → ℝ)) :=
  {xη |
    xη.1 ∈ X ∧
      (∀ i : Fin s, ∀ k : Fin (qK i), xη.2 i ≤ u i k ⬝ᵥ benders_residual (A i) (b i) xη.1) ∧
      ∀ i : Fin s, ∀ j : Fin (qJ i), 0 ≤ r i j ⬝ᵥ benders_residual (A i) (b i) xη.1}

/-- Membership in `separable_benders_master_feasible_set A b X u r` means satisfying the master
restriction `x ∈ X`, every blockwise optimality cut, and every blockwise feasibility cut. -/
theorem mem_separable_benders_master_feasible_set_iff
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (xη : (Fin n → ℝ) × (Fin s → ℝ)) :
    xη ∈ separable_benders_master_feasible_set A b X u r ↔
      xη.1 ∈ X ∧
        (∀ i : Fin s, ∀ k : Fin (qK i),
          xη.2 i ≤ u i k ⬝ᵥ benders_residual (A i) (b i) xη.1) ∧
        ∀ i : Fin s, ∀ j : Fin (qJ i),
          0 ≤ r i j ⬝ᵥ benders_residual (A i) (b i) xη.1 :=
  Iff.rfl

/-- The separable master feasible set consists of a global master restriction `x ∈ X` together
with blockwise membership in the ordinary Benders master feasible sets. -/
theorem mem_separable_benders_master_feasible_set_iff_forall_mem_benders_master_feasible_set
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (xη : (Fin n → ℝ) × (Fin s → ℝ)) :
    xη ∈ separable_benders_master_feasible_set A b X u r ↔
      xη.1 ∈ X ∧
        ∀ i : Fin s,
          (xη.1, xη.2 i) ∈ benders_master_feasible_set (A i) (b i) Set.univ (u i) (r i) := by
  rw [mem_separable_benders_master_feasible_set_iff]
  constructor
  · intro hxη
    refine ⟨hxη.1, ?_⟩
    intro i
    rw [mem_benders_master_feasible_set_iff]
    exact ⟨Set.mem_univ _, hxη.2.1 i, hxη.2.2 i⟩
  · intro hxη
    refine ⟨hxη.1, ?_, ?_⟩
    · intro i k
      have hi :=
        (mem_benders_master_feasible_set_iff
          (A i)
          (b i)
          Set.univ
          (u i)
          (r i)
          (xη.1, xη.2 i)).1
          (hxη.2 i)
      exact hi.2.1 k
    · intro i j
      have hi :=
        (mem_benders_master_feasible_set_iff
          (A i)
          (b i)
          Set.univ
          (u i)
          (r i)
          (xη.1, xη.2 i)).1
          (hxη.2 i)
      exact hi.2.2 j

/-- The value of the separable reformulation from Exercise 8.19(i), namely the maximum of
`c x + ∑_i η_i` over the blockwise master feasible pairs `(x, η)`. -/
noncomputable def separable_benders_master_value
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (c : Fin n → ℝ) : ℝ :=
  sSup
    ((fun xη : (Fin n → ℝ) × (Fin s → ℝ) ↦
        c ⬝ᵥ xη.1 + ∑ i : Fin s, xη.2 i) ''
      separable_benders_master_feasible_set A b X u r)

/-- Helper for Exercise 8.19: two sets of real numbers
have the same supremum when the first is pointwise dominated by the second and is strictly
cofinal below every member of the second. -/
lemma sSup_eq_of_mutually_cofinal
    (S T : Set ℝ)
    (hST : ∀ a ∈ S, ∃ b ∈ T, a ≤ b)
    (hTS : ∀ b ∈ T, ∀ z < b, ∃ a ∈ S, z < a) :
    sSup S = sSup T := by
  -- First dispose of the empty cases, which use the strict cofinality hypothesis asymmetrically.
  rcases S.eq_empty_or_nonempty with hS | hS
  · subst S
    have hT : T = ∅ := by
      ext b
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hb
      have hb_sub_one : b - 1 < b := by
        linarith
      obtain ⟨a, ha, _⟩ := hTS b hb (b - 1) hb_sub_one
      exact ha
    subst T
    rfl
  rcases T.eq_empty_or_nonempty with hT | hT
  · subst T
    rcases hS with ⟨a, ha⟩
    obtain ⟨b, hb, _⟩ := hST a ha
    exact hb.elim
  -- In the bounded case, compare both suprema directly with their defining order properties.
  by_cases hT_bdd : BddAbove T
  · have hS_bdd : BddAbove S := by
      rcases hT_bdd with ⟨bound, hbound⟩
      refine ⟨bound, ?_⟩
      intro a ha
      obtain ⟨b, hb, hab⟩ := hST a ha
      exact hab.trans (hbound hb)
    apply le_antisymm
    · refine csSup_le hS ?_
      intro a ha
      obtain ⟨b, hb, hab⟩ := hST a ha
      exact hab.trans (le_csSup hT_bdd hb)
    · refine csSup_le hT ?_
      intro b hb
      by_contra hnot
      have hsup_lt : sSup S < b := lt_of_not_ge hnot
      obtain ⟨a, ha, hsup_a⟩ := hTS b hb (sSup S) hsup_lt
      exact (not_lt_of_ge (le_csSup hS_bdd ha)) hsup_a
  -- If the second set is unbounded, strict cofinality forces the first to be unbounded as well.
  · have hS_not_bdd : ¬ BddAbove S := by
      intro hS_bdd
      apply hT_bdd
      rcases hS_bdd with ⟨bound, hbound⟩
      refine ⟨bound + 1, ?_⟩
      intro b hb
      by_contra hnot
      have hbound_succ : bound < bound + 1 := by
        linarith
      have hbound_lt : bound < b := lt_trans hbound_succ (lt_of_not_ge hnot)
      obtain ⟨a, ha, hbound_a⟩ := hTS b hb bound hbound_lt
      exact (not_lt_of_ge (hbound ha)) hbound_a
    rw [csSup_of_not_bddAbove hS_not_bdd, csSup_of_not_bddAbove hT_bdd]

/-- Helper for Exercise 8.19: every feasible primal
subproblem objective is bounded above by every feasible dual objective. -/
lemma bendersSubproblemObjective_le_dualObjective
    (G : Matrix (Fin m) (Fin n) ℝ)
    (h : Fin n → ℝ)
    (rhs : Fin m → ℝ)
    (v : Fin m → ℝ)
    (y : Fin n → ℝ)
    (hv : v ∈ benders_dual_polyhedron G h)
    (hy : y ∈ benders_subproblem_feasible_set G rhs) :
    h ⬝ᵥ y ≤ v ⬝ᵥ rhs := by
  -- Compare through `(v ᵥ* G) ⬝ᵥ y`, using nonnegativity on the appropriate side.
  have hv_data := (mem_benders_dual_polyhedron_iff G h v).1 hv
  have hy_data := (mem_benders_subproblem_feasible_set_iff G rhs y).1 hy
  calc
    h ⬝ᵥ y ≤ (v ᵥ* G) ⬝ᵥ y :=
      dotProduct_le_dotProduct_of_nonneg_right hv_data.2 hy_data.2
    _ = v ⬝ᵥ (G *ᵥ y) := (Matrix.dotProduct_mulVec v G y).symm
    _ ≤ v ⬝ᵥ rhs :=
      dotProduct_le_dotProduct_of_nonneg_left hy_data.1 hv_data.1

/-- Helper for Exercise 8.19: a Benders projection is
characterized by all cuts from a representative family of extreme rays. -/
lemma mem_bendersProjectionSet_iff_extremeRayCuts
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    {qJ : ℕ}
    (r : Fin qJ → Fin m → ℝ)
    (hrays : IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone G) r)
    (x : Fin n → ℝ) :
    x ∈ benders_projection_set A G b ↔
      ∀ j : Fin qJ, 0 ≤ r j ⬝ᵥ benders_residual A b x := by
  -- Rewrite the projection by the imported extreme-ray theorem, then expose cut membership.
  rw [bendersProjectionSet_eq_feasibilityCutSet_ofExtremeRays A G b r hrays]
  exact mem_benders_feasibility_cut_set_iff A b r x

/-- Helper for Exercise 8.19: feasible extreme-point cuts
can be approximated from below by an actual feasible subproblem objective. -/
lemma exists_bendersSubproblemPoint_gt_sub_of_extremePointCuts
    (A : Matrix (Fin m) (Fin n) ℝ)
    (G : Matrix (Fin m) (Fin p) ℝ)
    (b : Fin m → ℝ)
    (h : Fin p → ℝ)
    {qK : ℕ}
    (u : Fin qK → Fin m → ℝ)
    (hpoints : IsExtremePointRepresentativeFamily (benders_dual_polyhedron G h) u)
    (x : Fin n → ℝ)
    (eta epsilon : ℝ)
    (hx : x ∈ benders_projection_set A G b)
    (hcuts : ∀ k : Fin qK, eta ≤ u k ⬝ᵥ benders_residual A b x)
    (hepsilon : 0 < epsilon) :
    ∃ y : Fin p → ℝ,
      y ∈ benders_subproblem_feasible_set G (benders_residual A b x) ∧
        eta - epsilon < h ⬝ᵥ y := by
  -- The cut value bounds `eta`, and the imported block theorem identifies it with the primal
  -- `EReal` supremum.
  have heta_mem : eta ∈ benders_optimality_cut_set A b u x :=
    (mem_benders_optimality_cut_set_iff A b u x eta).2 hcuts
  have heta_le_cut :
      (eta : EReal) ≤ benders_optimality_cut_value A b u x :=
    le_sSup (Set.mem_image_of_mem (fun value : ℝ ↦ (value : EReal)) heta_mem)
  have heta_le_value :
      (eta : EReal) ≤ benders_subproblem_value G h (benders_residual A b x) := by
    rw [bendersSubproblemValue_eq_optimalityCutValue_ofExtremePoints A G b h u hpoints x hx]
    exact heta_le_cut
  have hbelow_lt_value :
      ((eta - epsilon : ℝ) : EReal) <
        benders_subproblem_value G h (benders_residual A b x) :=
    (EReal.coe_lt_coe (sub_lt_self eta hepsilon)).trans_le heta_le_value
  -- Unpack the supremum witness; its image equation converts the `EReal` inequality back to ℝ.
  rw [benders_subproblem_value] at hbelow_lt_value
  obtain ⟨value, ⟨y, hy, hy_value⟩, hvalue⟩ := lt_sSup_iff.mp hbelow_lt_value
  subst value
  refine ⟨y, hy, ?_⟩
  exact EReal.coe_lt_coe_iff.mp hvalue

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap08/section_8_5/ch8_sec8_5_exercise_8_19.lean

Exercise 8.19 (1). For the separable mixed problem
`z_I := max (c x + ∑_i h^i y^i)` subject to `A_i x + G_i y^i ≤ b^i`, `x ∈ X`, and
`y^i ∈ ℝ_+^{p_i}`, if for each block `i` the family `u i` represents the extreme points of the
dual polyhedron `Q_i = {u^i ≥ 0 | u^i G_i ≥ h^i}` and the family `r i` represents the extreme
rays of the cone `C_i = {u^i ≥ 0 | u^i G_i ≥ 0}`, then the problem can be reformulated as the
master problem maximizing `c x + ∑_i η_i` over `x ∈ X`, `η ∈ ℝ^s`, and the blockwise optimality
and feasibility cuts
`η_i ≤ u^{ik}(b^i - A_i x)` and `r^{ij}(b^i - A_i x) ≥ 0`. -/
theorem separable_benders_original_value_eq_master_value_of_extreme_families
    (A : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin n) ℝ)
    (G : ∀ i : Fin s, Matrix (Fin (rowDim i)) (Fin (colDim i)) ℝ)
    (b : ∀ i : Fin s, Fin (rowDim i) → ℝ)
    (X : Set (Fin n → ℝ))
    (c : Fin n → ℝ)
    (h : ∀ i : Fin s, Fin (colDim i) → ℝ)
    {qK qJ : Fin s → ℕ}
    (u : ∀ i : Fin s, Fin (qK i) → Fin (rowDim i) → ℝ)
    (r : ∀ i : Fin s, Fin (qJ i) → Fin (rowDim i) → ℝ)
    (hpoints :
      ∀ i : Fin s,
        IsExtremePointRepresentativeFamily (separable_benders_dual_polyhedron G h i) (u i))
    (hrays :
      ∀ i : Fin s,
        IsExtremeRayRepresentativeFamily (benders_feasibility_cone (G i)) (r i)) :
    separable_benders_original_value A G b X c h =
      separable_benders_master_value A b X u r c := by
  classical
  -- Compare the two real objective images through mutual cofinality rather than unfolding the
  -- imported block constructions inside the global supremum argument.
  unfold separable_benders_original_value separable_benders_master_value
  apply sSup_eq_of_mutually_cofinal
  · rintro value ⟨⟨x, y⟩, hxy, rfl⟩
    have hxy_data :=
      (mem_separable_benders_original_feasible_set_iff A G b X (x, y)).1 hxy
    let eta : Fin s → ℝ := fun i ↦ h i ⬝ᵥ y i
    refine ⟨c ⬝ᵥ x + ∑ i : Fin s, eta i, ?_, ?_⟩
    · refine ⟨(x, eta), ?_, rfl⟩
      rw [mem_separable_benders_master_feasible_set_iff]
      refine ⟨hxy_data.1, ?_, ?_⟩
      · intro i k
        have hpoints_i :
            IsExtremePointRepresentativeFamily
              (benders_dual_polyhedron (G i) (h i)) (u i) := by
          simpa only [separable_benders_dual_polyhedron, benders_dual_polyhedron] using
            hpoints i
        have hu_dual : u i k ∈ benders_dual_polyhedron (G i) (h i) :=
          (mem_extremePoints_iff_left.mp (hpoints_i.isExtremePoint k)).1
        exact bendersSubproblemObjective_le_dualObjective
          (G i) (h i) (benders_residual (A i) (b i) x) (u i k) (y i)
          hu_dual (hxy_data.2 i)
      · intro i j
        have hrays_i :
            IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone (G i)) (r i) := by
          simpa only [IsExtremeRayRepresentativeFamily,
            IsExtremeRayRepresentativeFamilyLocal, benders_feasibility_cone] using hrays i
        have hx_projection : x ∈ benders_projection_set (A i) (G i) (b i) :=
          (mem_benders_projection_set_iff (A i) (G i) (b i) x).2
            ⟨y i, hxy_data.2 i⟩
        exact
          (mem_bendersProjectionSet_iff_extremeRayCuts
            (A i) (G i) (b i) (r i) hrays_i x).1 hx_projection j
    · rfl
  · rintro value ⟨⟨x, eta⟩, hxeta, rfl⟩ z hz
    have hxeta_data :=
      (mem_separable_benders_master_feasible_set_iff A b X u r (x, eta)).1 hxeta
    let epsilon : ℝ :=
      (c ⬝ᵥ x + ∑ i : Fin s, eta i - z) / ((s : ℝ) + 1)
    have hdenominator_pos : 0 < (s : ℝ) + 1 :=
      add_pos_of_nonneg_of_pos (Nat.cast_nonneg s) zero_lt_one
    have hgap_pos : 0 < c ⬝ᵥ x + ∑ i : Fin s, eta i - z :=
      sub_pos.mpr hz
    have hepsilon : 0 < epsilon := by
      exact div_pos hgap_pos hdenominator_pos
    -- Apply the block approximation interface at the common error `epsilon` and choose all
    -- dependent witnesses simultaneously.
    have hblock :
        ∀ i : Fin s,
          ∃ yi : Fin (colDim i) → ℝ,
            yi ∈ benders_subproblem_feasible_set
              (G i) (benders_residual (A i) (b i) x) ∧
              eta i - epsilon < h i ⬝ᵥ yi := by
      intro i
      have hpoints_i :
          IsExtremePointRepresentativeFamily
            (benders_dual_polyhedron (G i) (h i)) (u i) := by
        simpa only [separable_benders_dual_polyhedron, benders_dual_polyhedron] using
          hpoints i
      have hrays_i :
          IsExtremeRayRepresentativeFamilyLocal (benders_dual_cone (G i)) (r i) := by
        simpa only [IsExtremeRayRepresentativeFamily,
          IsExtremeRayRepresentativeFamilyLocal, benders_feasibility_cone] using hrays i
      have hx_projection : x ∈ benders_projection_set (A i) (G i) (b i) :=
        (mem_bendersProjectionSet_iff_extremeRayCuts
          (A i) (G i) (b i) (r i) hrays_i x).2 (hxeta_data.2.2 i)
      exact exists_bendersSubproblemPoint_gt_sub_of_extremePointCuts
        (A i) (G i) (b i) (h i) (u i) hpoints_i x (eta i) epsilon
        hx_projection (hxeta_data.2.1 i) hepsilon
    choose y hy_feasible hy_lower using hblock
    refine ⟨c ⬝ᵥ x + ∑ i : Fin s, h i ⬝ᵥ y i, ?_, ?_⟩
    · refine ⟨(x, y), ?_, rfl⟩
      exact (mem_separable_benders_original_feasible_set_iff A G b X (x, y)).2
        ⟨hxeta_data.1, hy_feasible⟩
    · have hsum_le :
          ∑ i : Fin s, (eta i - epsilon) ≤ ∑ i : Fin s, h i ⬝ᵥ y i := by
        exact Finset.sum_le_sum fun i _ ↦ (hy_lower i).le
      have hsum_sub :
          (∑ i : Fin s, eta i) - (s : ℝ) * epsilon ≤
            ∑ i : Fin s, h i ⬝ᵥ y i := by
        simpa [Finset.sum_sub_distrib] using hsum_le
      have hdenominator_ne : (s : ℝ) + 1 ≠ 0 := ne_of_gt hdenominator_pos
      have hepsilon_scale :
          ((s : ℝ) + 1) * epsilon =
            c ⬝ᵥ x + ∑ i : Fin s, eta i - z := by
        dsimp [epsilon]
        field_simp
      have hindex_lt : (s : ℝ) < (s : ℝ) + 1 := by
        linarith
      have herror_lt :
          (s : ℝ) * epsilon < c ⬝ᵥ x + ∑ i : Fin s, eta i - z := by
        have hscaled := mul_lt_mul_of_pos_right hindex_lt hepsilon
        rw [hepsilon_scale] at hscaled
        exact hscaled
      linarith

#print axioms separable_benders_original_value_eq_master_value_of_extreme_families

/-- Exercise 8.19 (2). In the standard Benders reformulation of (8.32), the optimality-cut index
set `K` is the product of the blockwise extreme-point index sets `K_i`; therefore its cardinality
is the product of the cardinalities of the `K_i`. -/
theorem card_separable_benders_optimality_index
    (qK : Fin s → ℕ) :
    Fintype.card ((i : Fin s) → Fin (qK i)) = ∏ i : Fin s, qK i := by
  rw [Fintype.card_pi]
  simp

/-- Exercise 8.19 (3). In the standard Benders reformulation of (8.32), the feasibility-cut
index set `J` is the disjoint sum of the blockwise extreme-ray index sets `J_i`; therefore its
cardinality is the sum of the cardinalities of the `J_i`. -/
theorem card_separable_benders_feasibility_index
    (qJ : Fin s → ℕ) :
    Fintype.card (Σ i : Fin s, Fin (qJ i)) = ∑ i : Fin s, qJ i := by
  rw [Fintype.card_sigma]
  simp

end Exercise819

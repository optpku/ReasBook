import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1

open scoped Matrix

section Exercise76

/-- Helper for Exercise 7.6: for a `Fin (q + 1)`-indexed family in `ℝ^3`, affine independence is
equivalent to linear independence of the tail difference vectors based at the zeroth point. -/
theorem affineIndependent_iff_linearIndependent_tail_sub_fin3 {q : ℕ}
    (p : Fin (q + 1) → Fin 3 → ℝ) :
    AffineIndependent ℝ p ↔
      LinearIndependent ℝ (fun i : Fin q ↦ p i.succ - p 0) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ p 0]
  simpa [finSuccAboveEquiv_apply, vsub_eq_sub] using
    (linearIndependent_equiv (finSuccAboveEquiv (0 : Fin (q + 1))) :
      LinearIndependent ℝ
          ((fun i : {j : Fin (q + 1) // j ≠ 0} ↦ (p i -ᵥ p 0 : Fin 3 → ℝ)) ∘
            finSuccAboveEquiv (0 : Fin (q + 1))) ↔
        LinearIndependent ℝ
          (fun i : {j : Fin (q + 1) // j ≠ 0} ↦ (p i -ᵥ p 0 : Fin 3 → ℝ))).symm

/-- The example vertex `(1,1,0)` used in Exercise 7.6. -/
def exercise_7_6_v110 : Fin 3 → ℝ :=
  ![(1 : ℝ), 1, 0]

/-- The example vertex `(1,0,0)` used in Exercise 7.6. -/
def exercise_7_6_v100 : Fin 3 → ℝ :=
  ![(1 : ℝ), 0, 0]

/-- The example vertex `(0,1,0)` used in Exercise 7.6. -/
def exercise_7_6_v010 : Fin 3 → ℝ :=
  ![(0 : ℝ), 1, 0]

/-- The example vertex `(1,0,1)` used in Exercise 7.6. -/
def exercise_7_6_v101 : Fin 3 → ℝ :=
  ![(1 : ℝ), 0, 1]

/-- The example vertex `(0,1,1)` used in Exercise 7.6. -/
def exercise_7_6_v011 : Fin 3 → ℝ :=
  ![(0 : ℝ), 1, 1]

/-- The concrete binary set
`S = {(1,1,0), (1,0,0), (0,1,0), (1,0,1), (0,1,1)} ⊆ {0,1}^3`
used for Exercise 7.6, with zero-based coordinates on `Fin 3`. -/
def exercise_7_6_binary_example_set : Set (Fin 3 → ℝ) :=
  { exercise_7_6_v110,
    exercise_7_6_v100,
    exercise_7_6_v010,
    exercise_7_6_v101,
    exercise_7_6_v011 }

/-- Membership in `exercise_7_6_binary_example_set` means being one of the five explicit binary
points used in the example. -/
theorem mem_exercise_7_6_binary_example_set_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_7_6_binary_example_set ↔
      x = exercise_7_6_v110 ∨
        x = exercise_7_6_v100 ∨
        x = exercise_7_6_v010 ∨
        x = exercise_7_6_v101 ∨
        x = exercise_7_6_v011 := by
  simp [exercise_7_6_binary_example_set]

/-- The polytope `conv(S)` attached to the explicit Exercise 7.6 example. -/
def exercise_7_6_polytope : Set (Fin 3 → ℝ) :=
  convexHull ℝ exercise_7_6_binary_example_set

/-- The lifted coefficient vector `(1,1,1)` defining the lifted inequality `x₁ + x₂ + x₃ ≤ 2`.
-/
def exercise_7_6_lifted_coeffs : Fin 3 → ℝ :=
  ![(1 : ℝ), 1, 1]

/-- The lifted coefficient vector of the Exercise 7.6 example is exactly `(1,1,1)`. -/
theorem exercise_7_6_lifted_coeffs_eq :
    exercise_7_6_lifted_coeffs = ![(1 : ℝ), 1, 1] := rfl

/-- The face of `conv(S)` cut out by the lifted inequality `x₁ + x₂ + x₃ ≤ 2`. -/
def exercise_7_6_lifted_face : Set (Fin 3 → ℝ) :=
  {x | x ∈ exercise_7_6_polytope ∧ exercise_7_6_lifted_coeffs ⬝ᵥ x = 2}

/-- Membership in `exercise_7_6_lifted_face` means belonging to `conv(S)` and meeting the lifted
inequality at equality. -/
theorem mem_exercise_7_6_lifted_face_iff
    (x : Fin 3 → ℝ) :
    x ∈ exercise_7_6_lifted_face ↔
      x ∈ exercise_7_6_polytope ∧ exercise_7_6_lifted_coeffs ⬝ᵥ x = 2 := Iff.rfl

/-- Helper for Exercise 7.6: every listed example vertex belongs to the polytope `conv(S)`. -/
theorem mem_exercise_7_6_polytope_of_mem_example_set
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_7_6_binary_example_set) :
    x ∈ exercise_7_6_polytope := by
  -- The example vertices are exactly the generators of the defining convex hull.
  exact subset_convexHull ℝ exercise_7_6_binary_example_set hx

/-- Helper for Exercise 7.6: the lifted inequality `x₁ + x₂ + x₃ ≤ 2` is valid on the whole
example polytope. -/
theorem exercise_7_6_valid_lifted_inequality :
    ∀ ⦃x : Fin 3 → ℝ⦄, x ∈ exercise_7_6_polytope →
      exercise_7_6_lifted_coeffs ⬝ᵥ x ≤ 2 := by
  let halfspace : Set (Fin 3 → ℝ) :=
    {x | exercise_7_6_lifted_coeffs ⬝ᵥ x ≤ 2}
  have hvertices : exercise_7_6_binary_example_set ⊆ halfspace := by
    -- Each listed vertex satisfies the lifted inequality by direct evaluation.
    intro x hx
    rcases (mem_exercise_7_6_binary_example_set_iff x).1 hx with
      rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [halfspace, exercise_7_6_lifted_coeffs_eq, exercise_7_6_v110, exercise_7_6_v100,
        exercise_7_6_v010, exercise_7_6_v101, exercise_7_6_v011, dotProduct,
        Fin.sum_univ_three]
    all_goals
      norm_num
  have hhalfspace_convex : Convex ℝ halfspace := by
    -- The inequality halfspace is the linear preimage of `(-∞, 2]`.
    let f : Module.Dual ℝ (Fin 3 → ℝ) :=
      ∑ i, exercise_7_6_lifted_coeffs i • LinearMap.proj i
    have hpreimage :
        halfspace = f ⁻¹' Set.Iic (2 : ℝ) := by
      ext x
      simp [halfspace, f, exercise_7_6_lifted_coeffs_eq, dotProduct]
    rw [hpreimage]
    exact (convex_Iic (2 : ℝ)).linear_preimage f
  have hsubset : exercise_7_6_polytope ⊆ halfspace := by
    -- Validity on the generators extends to the whole convex hull.
    exact convexHull_min hvertices hhalfspace_convex
  intro x hx
  exact hsubset hx

/-- Helper for Exercise 7.6: a listed vertex belongs to the lifted face once it is tight for the
lifted inequality. -/
private theorem exercise_7_6_mem_liftedFace_of_mem_example_set_and_tight
    {x : Fin 3 → ℝ}
    (hx : x ∈ exercise_7_6_binary_example_set)
    (htight : exercise_7_6_lifted_coeffs ⬝ᵥ x = 2) :
    x ∈ exercise_7_6_lifted_face := by
  refine (mem_exercise_7_6_lifted_face_iff x).2 ?_
  exact ⟨mem_exercise_7_6_polytope_of_mem_example_set hx, htight⟩

/-- Helper for Exercise 7.6: the lifted face is the exposed subset cut out by maximizing
`x ↦ x₁ + x₂ + x₃` on `conv(S)`. -/
theorem exercise_7_6_lifted_face_isExposed :
    IsExposed ℝ exercise_7_6_polytope exercise_7_6_lifted_face := by
  let l : StrongDual ℝ (Fin 3 → ℝ) :=
    ∑ i, (1 : ℝ) • ContinuousLinearMap.proj i
  have hface :
      exercise_7_6_lifted_face = l.toExposed exercise_7_6_polytope := by
    ext x
    constructor
    · intro hx
      rcases (mem_exercise_7_6_lifted_face_iff x).1 hx with ⟨hxPolytope, hxEq⟩
      have hxEval : l x = 2 := by
        simpa [l, exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three] using hxEq
      refine ⟨hxPolytope, ?_⟩
      intro y hyPolytope
      have hyEval : l y ≤ 2 := by
        simpa [l, exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three] using
          exercise_7_6_valid_lifted_inequality hyPolytope
      simpa [hxEval] using hyEval
    · intro hx
      have hp : exercise_7_6_v110 ∈ exercise_7_6_polytope := by
        exact mem_exercise_7_6_polytope_of_mem_example_set (by
          simp [exercise_7_6_binary_example_set])
      have hx_ge : 2 ≤ l x := by
        have hmax := hx.2 exercise_7_6_v110 hp
        simpa [l, exercise_7_6_v110] using hmax
      have hx_le : l x ≤ 2 := by
        simpa [l, exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three] using
          exercise_7_6_valid_lifted_inequality hx.1
      have hxEval : l x = 2 := by
        linarith
      have hxEq : exercise_7_6_lifted_coeffs ⬝ᵥ x = 2 := by
        simpa [l, exercise_7_6_lifted_coeffs_eq, dotProduct, Fin.sum_univ_three] using hxEval
      exact (mem_exercise_7_6_lifted_face_iff x).2 ⟨hx.1, hxEq⟩
  rw [hface]
  exact ContinuousLinearMap.toExposed.isExposed

/-- Helper for Exercise 7.6: the four vertices `(1,0,0)`, `(1,1,0)`, `(1,0,1)`, and `(0,1,0)`
are affinely independent in `ℝ^3`. -/
theorem exercise_7_6_polytope_affineIndependentFamily :
    AffineIndependent ℝ
      ![exercise_7_6_v100, exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v010] := by
  rw [affineIndependent_iff_linearIndependent_tail_sub_fin3]
  let e1 : Fin 3 → ℝ := Pi.single 1 1
  let e2 : Fin 3 → ℝ := Pi.single 2 1
  let v : Fin 3 → ℝ := -Pi.single 0 1 + Pi.single 1 1
  have htail :
      (fun i : Fin 3 ↦
        ![exercise_7_6_v100, exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v010] i.succ -
          ![exercise_7_6_v100, exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v010] 0) =
        ![e1, e2, v] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e1, e2, v, exercise_7_6_v100, exercise_7_6_v110,
      exercise_7_6_v101, exercise_7_6_v010]
  rw [htail]
  have hpair : LinearIndependent ℝ ![e2, v] := by
    have he2_ne : e2 ≠ 0 := by
      intro hzero
      have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 2) hzero
      simpa [e2] using hcoord
    apply (LinearIndependent.pair_iff' he2_ne).2
    intro a ha
    have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 0) ha
    simpa [e2, v] using hcoord
  have he1_not_mem : e1 ∉ Submodule.span ℝ (Set.range ![e2, v]) := by
    intro he1_mem
    have he1_mem' : e1 ∈ Submodule.span ℝ ({v, e2} : Set (Fin 3 → ℝ)) := by
      simpa using he1_mem
    rcases (Submodule.mem_span_pair).1 he1_mem' with ⟨a, b, hab⟩
    have hcoord0 := congrArg (fun x : Fin 3 → ℝ ↦ x 0) hab
    have hcoord1 := congrArg (fun x : Fin 3 → ℝ ↦ x 1) hab
    have hcoord2 := congrArg (fun x : Fin 3 → ℝ ↦ x 2) hab
    simp [e1, e2, v] at hcoord0 hcoord1 hcoord2
    linarith
  exact hpair.finCons he1_not_mem

/-- Helper for Exercise 7.6: the three tight vertices `(1,1,0)`, `(1,0,1)`, and `(0,1,1)` are
affinely independent. -/
theorem exercise_7_6_lifted_face_affineIndependentFamily :
    AffineIndependent ℝ
      ![exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v011] := by
  rw [affineIndependent_iff_linearIndependent_tail_sub_fin3]
  let v1 : Fin 3 → ℝ := ![(0 : ℝ), -1, 1]
  let v2 : Fin 3 → ℝ := ![(-1 : ℝ), 0, 1]
  have htail :
      (fun i : Fin 2 ↦
        ![exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v011] i.succ -
          ![exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v011] 0) =
        ![v1, v2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [v1, v2, exercise_7_6_v110, exercise_7_6_v101,
      exercise_7_6_v011]
  rw [htail]
  have hv1_ne : v1 ≠ 0 := by
    intro hv1_zero
    have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 2) hv1_zero
    simpa [v1] using hcoord
  apply (LinearIndependent.pair_iff' hv1_ne).2
  intro a ha
  have hcoord := congrArg (fun x : Fin 3 → ℝ ↦ x 0) ha
  -- The first coordinate again isolates the scalar coefficient.
  simpa [v1, v2] using hcoord

/-- Helper for Exercise 7.6: four affinely independent points in `ℝ^3` already span the ambient
affine space. -/
private theorem affineSpan_eq_top_of_affineIndependentFamily
    {P : Set (Fin 3 → ℝ)} {p : Fin 4 → Fin 3 → ℝ}
    (hp : AffineIndependent ℝ p)
    (hp_range : Set.range p ⊆ P) :
    affineSpan ℝ P = ⊤ := by
  have hp_top : affineSpan ℝ (Set.range p) = ⊤ := by
    -- A `Fin 4`-indexed affinely independent family in `ℝ^3` has maximal affine span.
    exact
      (hp.affineSpan_eq_top_iff_card_eq_finrank_add_one).2
        (by simp [Module.finrank_fintype_fun_eq_card])
  apply top_unique
  have hle : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ P :=
    affineSpan_mono ℝ hp_range
  simpa [hp_top] using hle

/-- Helper for Exercise 7.6: the ambient polytope has affine dimension `3`. -/
theorem exercise_7_6_polytope_finrank_direction_affineSpan :
    Module.finrank ℝ (affineSpan ℝ exercise_7_6_polytope).direction = 3 := by
  let p : Fin 4 → Fin 3 → ℝ :=
    ![exercise_7_6_v100, exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v010]
  have hp_affineIndependent : AffineIndependent ℝ p := by
    simpa [p] using exercise_7_6_polytope_affineIndependentFamily
  have hp_range : Set.range p ⊆ exercise_7_6_polytope := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · exact mem_exercise_7_6_polytope_of_mem_example_set (by
        simp [exercise_7_6_binary_example_set])
    · exact mem_exercise_7_6_polytope_of_mem_example_set (by
        simp [exercise_7_6_binary_example_set])
    · exact mem_exercise_7_6_polytope_of_mem_example_set (by
        simp [exercise_7_6_binary_example_set])
    · exact mem_exercise_7_6_polytope_of_mem_example_set (by
        simp [exercise_7_6_binary_example_set])
  have htop : affineSpan ℝ exercise_7_6_polytope = ⊤ :=
    affineSpan_eq_top_of_affineIndependentFamily hp_affineIndependent hp_range
  rw [htop, AffineSubspace.direction_top, finrank_top]
  simp [Module.finrank_fintype_fun_eq_card]

/-- Helper for Exercise 7.6: the linear map `x ↦ c ⬝ᵥ x` written coordinatewise. -/
private def dotProductLinearMap (c : Fin 3 → ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, c i • LinearMap.proj i

/-- Helper for Exercise 7.6: `dotProductLinearMap c` evaluates as `c ⬝ᵥ x`. -/
private theorem dotProductLinearMap_apply
    (c x : Fin 3 → ℝ) :
    dotProductLinearMap c x = c ⬝ᵥ x := by
  simp [dotProductLinearMap, dotProduct]

/-- Helper for Exercise 7.6: the lifted dot-product map is nonzero. -/
private theorem exercise_7_6_liftedLinearMap_ne_zero :
    dotProductLinearMap exercise_7_6_lifted_coeffs ≠ 0 := by
  intro hzero
  have hvalue := congrArg (fun L : (Fin 3 → ℝ) →ₗ[ℝ] ℝ ↦ L (Pi.single 0 1)) hzero
  simpa [dotProductLinearMap_apply, exercise_7_6_lifted_coeffs_eq, dotProduct,
    Fin.sum_univ_three] using hvalue

/-- Helper for Exercise 7.6: every direction vector of the lifted face lies in the kernel of the
lifted dot-product map. -/
private theorem exercise_7_6_lifted_face_direction_le_ker :
    (affineSpan ℝ exercise_7_6_lifted_face).direction ≤
      LinearMap.ker (dotProductLinearMap exercise_7_6_lifted_coeffs) := by
  have hx0_tight : exercise_7_6_lifted_coeffs ⬝ᵥ exercise_7_6_v110 = 2 := by
    simp [exercise_7_6_lifted_coeffs_eq, exercise_7_6_v110, dotProduct, Fin.sum_univ_three]
  have hx0 : exercise_7_6_v110 ∈ exercise_7_6_lifted_face := by
    exact exercise_7_6_mem_liftedFace_of_mem_example_set_and_tight
      (by simp [exercise_7_6_binary_example_set]) hx0_tight
  let H : AffineSubspace ℝ (Fin 3 → ℝ) :=
    AffineSubspace.mk' exercise_7_6_v110
      (LinearMap.ker (dotProductLinearMap exercise_7_6_lifted_coeffs))
  have hF_le_H : exercise_7_6_lifted_face ⊆ H := by
    intro x hx
    -- Two points in the lifted face satisfy the same equality, so their difference is in the
    -- kernel of the lifted dot-product map.
    change x -ᵥ exercise_7_6_v110 ∈
      LinearMap.ker (dotProductLinearMap exercise_7_6_lifted_coeffs)
    refine LinearMap.mem_ker.2 ?_
    have hxEq : exercise_7_6_lifted_coeffs ⬝ᵥ x = 2 :=
      ((mem_exercise_7_6_lifted_face_iff x).1 hx).2
    simp [dotProductLinearMap_apply, vsub_eq_sub, hxEq, hx0_tight]
  have h_aff_le : affineSpan ℝ exercise_7_6_lifted_face ≤ H := (affineSpan_le).2 hF_le_H
  simpa [H] using
    (AffineSubspace.direction_le h_aff_le :
      (affineSpan ℝ exercise_7_6_lifted_face).direction ≤ H.direction)

/-- Helper for Exercise 7.6: the lifted equality face has affine dimension `2`. -/
theorem exercise_7_6_lifted_face_finrank_direction_affineSpan :
    Module.finrank ℝ (affineSpan ℝ exercise_7_6_lifted_face).direction = 2 := by
  let p : Fin 3 → Fin 3 → ℝ :=
    ![exercise_7_6_v110, exercise_7_6_v101, exercise_7_6_v011]
  have hp_affineIndependent : AffineIndependent ℝ p := by
    simpa [p] using exercise_7_6_lifted_face_affineIndependentFamily
  have hp_range : Set.range p ⊆ exercise_7_6_lifted_face := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    fin_cases i
    · have htight : exercise_7_6_lifted_coeffs ⬝ᵥ exercise_7_6_v110 = 2 := by
        simp [exercise_7_6_lifted_coeffs_eq, exercise_7_6_v110, dotProduct,
          Fin.sum_univ_three]
      exact exercise_7_6_mem_liftedFace_of_mem_example_set_and_tight
        (by simp [exercise_7_6_binary_example_set]) htight
    · have htight : exercise_7_6_lifted_coeffs ⬝ᵥ exercise_7_6_v101 = 2 := by
        simp [exercise_7_6_lifted_coeffs_eq, exercise_7_6_v101, dotProduct,
          Fin.sum_univ_three]
      exact exercise_7_6_mem_liftedFace_of_mem_example_set_and_tight
        (by simp [exercise_7_6_binary_example_set]) htight
    · have htight : exercise_7_6_lifted_coeffs ⬝ᵥ exercise_7_6_v011 = 2 := by
        simp [exercise_7_6_lifted_coeffs_eq, exercise_7_6_v011, dotProduct,
          Fin.sum_univ_three]
      exact exercise_7_6_mem_liftedFace_of_mem_example_set_and_tight
        (by simp [exercise_7_6_binary_example_set]) htight
  have hspan_le : affineSpan ℝ (Set.range p) ≤ affineSpan ℝ exercise_7_6_lifted_face :=
    affineSpan_mono ℝ hp_range
  have hp_dim :
      Module.finrank ℝ (affineSpan ℝ (Set.range p)).direction = 2 := by
    rw [direction_affineSpan]
    have hcard :
        Module.finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 = 3 := by
      simpa using
        (AffineIndependent.finrank_vectorSpan_add_one (k := ℝ) (p := p) hp_affineIndependent)
    omega
  have hface_dim_lower :
      2 ≤ Module.finrank ℝ (affineSpan ℝ exercise_7_6_lifted_face).direction := by
    simpa [hp_dim] using
      Submodule.finrank_mono (AffineSubspace.direction_le hspan_le)
  have hker_dim :
      Module.finrank ℝ (LinearMap.ker (dotProductLinearMap exercise_7_6_lifted_coeffs)) = 2 := by
    have hker_add_one :
        Module.finrank ℝ (LinearMap.ker (dotProductLinearMap exercise_7_6_lifted_coeffs)) + 1 =
          3 := by
      let f : Module.Dual ℝ (Fin 3 → ℝ) := dotProductLinearMap exercise_7_6_lifted_coeffs
      have hf : f ≠ 0 := by
        simpa [f] using exercise_7_6_liftedLinearMap_ne_zero
      simpa [f, Module.finrank_fintype_fun_eq_card] using f.finrank_ker_add_one_of_ne_zero hf
    omega
  have hface_dim_upper :
      Module.finrank ℝ (affineSpan ℝ exercise_7_6_lifted_face).direction ≤ 2 := by
    simpa [hker_dim] using
      Submodule.finrank_mono exercise_7_6_lifted_face_direction_le_ker
  exact le_antisymm hface_dim_upper hface_dim_lower

/-- Exercise 7.6 (3). For
`S = {(1,1,0), (1,0,0), (0,1,0), (1,0,1), (0,1,1)} ⊆ {0,1}^3`,
lifting the base inequality `x₁ + x₂ ≤ 2` on the slice `x₃ = 0` to
`x₁ + x₂ + x₃ ≤ 2` yields a facet of `conv(S)`. -/
theorem exercise_7_6_lifted_inequality_defines_facet :
    IsFacetOf exercise_7_6_polytope exercise_7_6_lifted_face := by
  have hp0_tight : exercise_7_6_lifted_coeffs ⬝ᵥ exercise_7_6_v110 = 2 := by
    simp [exercise_7_6_lifted_coeffs_eq, exercise_7_6_v110, dotProduct, Fin.sum_univ_three]
  have hp0 : exercise_7_6_v110 ∈ exercise_7_6_lifted_face := by
    -- The vertex `(1,1,0)` is tight for the lifted inequality.
    exact exercise_7_6_mem_liftedFace_of_mem_example_set_and_tight
      (by simp [exercise_7_6_binary_example_set]) hp0_tight
  rw [isFacetOf_iff]
  refine ⟨⟨exercise_7_6_v110, hp0⟩, exercise_7_6_lifted_face_isExposed, ?_⟩
  -- The explicit affine-dimension computations give the codimension-one relation.
  calc
    Module.finrank ℝ (affineSpan ℝ exercise_7_6_lifted_face).direction + 1
        = 2 + 1 := by rw [exercise_7_6_lifted_face_finrank_direction_affineSpan]
    _ = 3 := by norm_num
    _ = Module.finrank ℝ (affineSpan ℝ exercise_7_6_polytope).direction := by
      rw [exercise_7_6_polytope_finrank_direction_affineSpan]

end Exercise76

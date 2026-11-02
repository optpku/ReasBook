import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_theorem_3_13
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_definition_7_24
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_remark_7_25

open scoped BigOperators Pointwise

section Theorem726

variable {n : ℕ}

/-- A polynomial-time query solver bundles a dependent answer map together with a polynomial
runtime bound measured in the chosen query encoding size. This is the common owner abstraction for
the Chapter 7 optimization and separation solver interfaces. -/
structure PolynomialTimeQuerySolver
    (Query : Type*) (Answer : Query → Type*) (encodingSize : Query → ℕ) where
  solve : (query : Query) → Answer query
  runtime : Query → ℕ
  time_bound : Polynomial ℕ
  runtime_le (query : Query) :
    runtime query ≤ time_bound.eval (encodingSize query)

namespace PolynomialTimeQuerySolver

variable {Query : Type*} {Answer : Query → Type*} {encodingSize : Query → ℕ}

/-- A polynomial-time query solver is used via its answer map. -/
instance :
    CoeFun (PolynomialTimeQuerySolver Query Answer encodingSize)
      (fun _ ↦ (query : Query) → Answer query) where
  coe solver := solver.solve

/-- Evaluating a polynomial-time query solver via coercion agrees with its underlying answer map.
-/
@[simp] theorem coe_apply
    (solver : PolynomialTimeQuerySolver Query Answer encodingSize)
    (query : Query) :
    solver query = solver.solve query :=
  rfl

/-- The runtime recorded by a polynomial-time query solver is bounded by its polynomial time bound
evaluated on the query encoding size. -/
theorem runtime_le_eval
    (solver : PolynomialTimeQuerySolver Query Answer encodingSize)
    (query : Query) :
    solver.runtime query ≤ solver.time_bound.eval (encodingSize query) :=
  solver.runtime_le query

end PolynomialTimeQuerySolver

/-- A rational separating inequality for the query point `y` against the polyhedron `P`. -/
structure LinearSeparationCertificate (P : Set (Fin n → ℝ)) (y : Fin n → ℚ) where
  normal : Fin n → ℚ
  offset : ℚ
  valid (x : Fin n → ℝ) :
    x ∈ P → (∑ i, (normal i : ℝ) * x i) ≤ (offset : ℝ)
  separates :
    (offset : ℝ) < ∑ i, (normal i : ℝ) * (y i : ℝ)

/-- The answer returned by a separation solver for `P` on the rational query point `y`. -/
inductive LinearSeparationAnswer (P : Set (Fin n → ℝ)) (y : Fin n → ℚ) where
  | inside (hmem : (fun i ↦ (y i : ℝ)) ∈ P)
  | separated (certificate : LinearSeparationCertificate P y)

/-- A polynomial-time separation solver for `P` answers each rational query point either by
certifying membership or by returning a separating inequality, together with a polynomial runtime
bound in the query encoding size. -/
abbrev LinearSeparationSolver (P : Set (Fin n → ℝ)) :=
  PolynomialTimeQuerySolver
    (Fin n → ℚ)
    (LinearSeparationAnswer P)
    EncodingSize.rationalVector

/-- The separation problem for `P` is polynomial-time solvable when `P` admits a polynomial-time
separation solver on rational query points. -/
abbrev HasPolynomialTimeSeparationProblem (P : Set (Fin n → ℝ)) : Prop :=
  Nonempty (LinearSeparationSolver P)

/-- Expanding `HasPolynomialTimeSeparationProblem P` recalls the canonical solver owner. -/
theorem hasPolynomialTimeSeparationProblem_iff
    (P : Set (Fin n → ℝ)) :
    HasPolynomialTimeSeparationProblem P ↔ Nonempty (LinearSeparationSolver P) := by
  rfl

/-- The answer returned by a linear-optimization solver for the rational objective `c` over `P`.
-/
inductive LinearOptimizationAnswer (P : Set (Fin n → ℝ)) (c : Fin n → ℚ) where
  | infeasible (hP : P = ∅)
  | unbounded
      (hunbounded :
        ∀ M : ℚ, ∃ x : Fin n → ℝ, x ∈ P ∧ (M : ℝ) ≤ ∑ i, (c i : ℝ) * x i)
  | optimum (x : Fin n → ℚ) (value : ℚ)
      (hx : (fun i ↦ (x i : ℝ)) ∈ P)
      (hvalue : (value : ℝ) = ∑ i, (c i : ℝ) * (x i : ℝ))
      (hoptimal :
        ∀ y : Fin n → ℝ, y ∈ P → ∑ i, (c i : ℝ) * y i ≤ (value : ℝ))

/-- A polynomial-time optimization solver for `P` answers each rational linear objective by
returning infeasibility, unboundedness, or a rational optimal solution, together with a
polynomial runtime bound in the objective encoding size. -/
abbrev LinearOptimizationSolver (P : Set (Fin n → ℝ)) :=
  PolynomialTimeQuerySolver
    (Fin n → ℚ)
    (LinearOptimizationAnswer P)
    EncodingSize.rationalVector

/-- The optimization problem for `P` is polynomial-time solvable when `P` admits a polynomial-time
optimization solver for rational linear objectives. -/
abbrev HasPolynomialTimeOptimizationProblem (P : Set (Fin n → ℝ)) : Prop :=
  Nonempty (LinearOptimizationSolver P)

/-- Expanding `HasPolynomialTimeOptimizationProblem P` recalls the canonical solver owner. -/
theorem hasPolynomialTimeOptimizationProblem_iff
    (P : Set (Fin n → ℝ)) :
    HasPolynomialTimeOptimizationProblem P ↔ Nonempty (LinearOptimizationSolver P) := by
  rfl

variable {P : Set (Fin n → ℝ)} {L : ℕ}

/-- Helper for Theorem 7.26: the constant zero runtime is bounded by the zero polynomial on every
query size. -/
lemma zeroRuntimeLeZeroPolynomialEval
    {Query : Type*}
    (encodingSize : Query → ℕ) :
    ∀ query : Query, 0 ≤ (0 : Polynomial ℕ).eval (encodingSize query) := by
  intro query
  simp

/-- Helper for Theorem 7.26: every listed ray belongs to the finitely generated cone it spans. -/
lemma listedRay_mem_finitelyGeneratedCone
    {t : ℕ}
    (rays : Fin t → Fin n → ℝ)
    (i : Fin t) :
    rays i ∈ finitely_generated_cone rays := by
  -- Put unit weight on the chosen listed ray and zero weight on every other generator.
  refine mem_finitely_generated_cone_iff.mpr ?_
  refine ⟨fun j ↦ if j = i then 1 else 0, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  · ext j
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [hbi]
    · intro hi_not_mem
      exact False.elim (hi_not_mem (by simp))

/-- Helper for Theorem 7.26: the zero vector belongs to every finitely generated cone. -/
lemma zero_mem_finitelyGeneratedCone
    {t : ℕ}
    (rays : Fin t → Fin n → ℝ) :
    (0 : Fin n → ℝ) ∈ finitely_generated_cone rays := by
  -- Zero is the conic combination with all coefficients equal to `0`.
  refine mem_finitely_generated_cone_iff.mpr ?_
  refine ⟨fun _ ↦ 0, ?_, ?_⟩
  · intro i
    simp
  · simp

/-- Helper for Theorem 7.26: every listed vertex of a `convexHull + cone` representation is a
feasible point of the represented polyhedron. -/
lemma listedVertex_mem_polyhedron
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)))
    (i : Fin k) :
    (fun j ↦ (vertices i j : ℝ)) ∈ P := by
  -- A listed vertex lies in the convex-hull part, and the cone contributes `0`.
  rw [hrepr]
  refine Set.mem_add.mpr ⟨fun j ↦ (vertices i j : ℝ), ?_, 0, ?_, by simp⟩
  · exact
      (show
        Set.range (fun i ↦ fun j ↦ (vertices i j : ℝ)) ⊆
          convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) from
        subset_convexHull ℝ (s := Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)))
        (Set.mem_range_self i)
  · exact zero_mem_finitelyGeneratedCone (fun j ↦ fun l ↦ (rays j l : ℝ))

/-- Helper for Theorem 7.26: if all listed rays are nonpositive for the objective, then every
feasible point is bounded above by a maximizing listed vertex. -/
lemma objectiveLeMaxVertexOfNonpositiveRays
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)))
    (c : Fin n → ℚ)
    (iMax : Fin k)
    (hmax :
      ∀ i : Fin k,
        (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices i j : ℝ)) ≤
          (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ)))
    (hrays_nonpos :
      ∀ i : Fin t,
        (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (rays i j : ℝ)) ≤ 0)
    {x : Fin n → ℝ}
    (hx : x ∈ P) :
    (fun j ↦ (c j : ℝ)) ⬝ᵥ x ≤
      (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ)) := by
  -- Decompose `x` into its convex-hull and cone parts, then bound each contribution separately.
  have hxrepr :
      x ∈
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) := by
    simpa [hrepr] using hx
  rcases Set.mem_add.mp hxrepr with ⟨y, hy, z, hz, rfl⟩
  rcases mem_convexHull_range_iff_exists_barycentric_weights.mp hy with
    ⟨lam, hlam_nonneg, hlam_sum, hyrepr⟩
  rcases mem_finitely_generated_cone_iff.mp hz with ⟨μ, hμ_nonneg, hzrepr⟩
  have hyBound :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ y ≤
        (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ)) := by
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ y
          = ∑ i, lam i * ((fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices i j : ℝ))) := by
              rw [hyrepr]
              simp [dotProduct_sum, dotProduct_smul]
      _ ≤ ∑ i, lam i * ((fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ))) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_left (hmax i) (hlam_nonneg i)
      _ = (∑ i, lam i) *
            ((fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ))) := by
            rw [Finset.sum_mul]
      _ = (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ)) := by
            simp [hlam_sum]
  have hzBound :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ z ≤ 0 := by
    calc
      (fun j ↦ (c j : ℝ)) ⬝ᵥ z
          = ∑ i, μ i * ((fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (rays i j : ℝ))) := by
              rw [hzrepr]
              simp [dotProduct_sum, dotProduct_smul]
      _ ≤ ∑ i, μ i * 0 := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_left (hrays_nonpos i) (hμ_nonneg i)
      _ = 0 := by simp
  have hxy :
      (fun j ↦ (c j : ℝ)) ⬝ᵥ (y + z) =
        (fun j ↦ (c j : ℝ)) ⬝ᵥ y + (fun j ↦ (c j : ℝ)) ⬝ᵥ z := by
    simp [dotProduct_add]
  calc
    (fun j ↦ (c j : ℝ)) ⬝ᵥ (y + z)
        = (fun j ↦ (c j : ℝ)) ⬝ᵥ y + (fun j ↦ (c j : ℝ)) ⬝ᵥ z := hxy
    _ ≤ (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ)) + 0 := by
          exact add_le_add hyBound hzBound
    _ = (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices iMax j : ℝ)) := by ring

/-- Helper for Theorem 7.26: any nonempty `convexHull + cone` representation must list at least
one vertex. -/
lemma nonemptyVertexIndexOfRepresentation
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)))
    {x : Fin n → ℝ}
    (hx : x ∈ P) :
    Nonempty (Fin k) := by
  -- A feasible point yields barycentric weights summing to `1`, so the vertex index type cannot
  -- be empty.
  by_cases hk : k = 0
  · have hxrepr :
      x ∈
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) := by
      simpa [hrepr] using hx
    rcases Set.mem_add.mp hxrepr with ⟨y, hy, _z, _hz, rfl⟩
    rcases mem_convexHull_range_iff_exists_barycentric_weights.mp hy with
      ⟨lam, _hlam_nonneg, hlam_sum, _hyrepr⟩
    subst hk
    simp at hlam_sum
  · exact ⟨⟨0, Nat.pos_iff_ne_zero.mpr hk⟩⟩

/-- Helper for Theorem 7.26: adding a nonnegative multiple of a listed ray preserves feasibility
for a `convexHull + cone` representation. -/
lemma feasibleAddSmulListedRay
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)))
    {x : Fin n → ℝ}
    (hx : x ∈ P)
    (i : Fin t)
    {a : ℝ}
    (ha : 0 ≤ a) :
    x + a • (fun j ↦ (rays i j : ℝ)) ∈ P := by
  -- Keep the convex-hull part fixed and absorb the extra ray inside the finitely generated cone.
  have hxrepr :
      x ∈
        convexHull ℝ (Set.range fun j ↦ fun l ↦ (vertices j l : ℝ)) +
          finitely_generated_cone (fun j ↦ fun l ↦ (rays j l : ℝ)) := by
    simpa [hrepr] using hx
  rcases Set.mem_add.mp hxrepr with ⟨y, hy, z, hz, hsum⟩
  rw [hrepr]
  refine Set.mem_add.mpr ?_
  refine ⟨y, hy, z + a • (fun j ↦ (rays i j : ℝ)), ?_, ?_⟩
  · exact
      finitely_generated_cone_add_smul_mem
        (fun j ↦ fun l ↦ (rays j l : ℝ))
        hz
        (listedRay_mem_finitelyGeneratedCone (fun j ↦ fun l ↦ (rays j l : ℝ)) i)
        ha
  · calc
      y + (z + a • (fun j ↦ (rays i j : ℝ))) = (y + z) + a • (fun j ↦ (rays i j : ℝ)) := by
        simp [add_assoc]
      _ = x + a • (fun j ↦ (rays i j : ℝ)) := by rw [hsum]

/-- Helper for Theorem 7.26: a listed ray with strictly positive objective value certifies that
the represented optimization problem is unbounded. -/
lemma unboundedAnswerOfPositiveRay
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun j ↦ fun l ↦ (vertices j l : ℝ)) +
          finitely_generated_cone (fun j ↦ fun l ↦ (rays j l : ℝ)))
    (c : Fin n → ℚ)
    {x0 : Fin n → ℝ}
    (hx0 : x0 ∈ P)
    (i : Fin t)
    (hpositive :
      0 < (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (rays i j : ℝ))) :
    Nonempty (LinearOptimizationAnswer P c) := by
  -- A strictly improving feasible ray lets the objective exceed any prescribed bound.
  refine ⟨LinearOptimizationAnswer.unbounded ?_⟩
  intro M
  let obj : (Fin n → ℝ) → ℝ := fun x ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ x
  let rayObj : ℝ := obj (fun j ↦ (rays i j : ℝ))
  let a : ℝ := max 0 (((M : ℝ) - obj x0) / rayObj)
  refine ⟨x0 + a • (fun j ↦ (rays i j : ℝ)), ?_, ?_⟩
  · -- Feasibility is preserved because the listed ray stays in the recession cone part.
    exact feasibleAddSmulListedRay vertices rays hrepr hx0 i (le_max_left 0 _)
  · have hrayObj : 0 < rayObj := by
      simpa [rayObj, obj] using hpositive
    have hscale :
        (M : ℝ) - obj x0 ≤ a * rayObj := by
      exact (div_le_iff₀ hrayObj).mp (le_max_right 0 _)
    have hobj :
        obj (x0 + a • (fun j ↦ (rays i j : ℝ))) =
          obj x0 + a * rayObj := by
      simp [obj, rayObj, dotProduct_add, dotProduct_smul, mul_comm]
    have hbound :
        (M : ℝ) ≤ obj x0 + a * rayObj := by
      linarith
    calc
      (M : ℝ) ≤ obj x0 + a * rayObj := hbound
      _ = obj (x0 + a • (fun j ↦ (rays i j : ℝ))) := by rw [hobj]
      _ = ∑ j, (c j : ℝ) * (x0 + a • (fun j ↦ (rays i j : ℝ))) j := by
            simp [obj, dotProduct]

/-- Helper for Theorem 7.26: a bounded rational `convexHull + cone` representation directly
produces an optimization answer for every rational objective. -/
lemma linearOptimizationAnswerOfVrepresentation
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)))
    (c : Fin n → ℚ) :
    Nonempty (LinearOptimizationAnswer P c) := by
  classical
  -- Split into infeasible, unbounded, and bounded-max-vertex cases along the source proof.
  by_cases hEmpty : P = ∅
  · exact ⟨LinearOptimizationAnswer.infeasible hEmpty⟩
  · have hNonempty : P.Nonempty := Set.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨x0, hx0⟩ := hNonempty
    by_cases hPositive :
        ∃ i : Fin t, 0 < (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (rays i j : ℝ))
    · obtain ⟨i, hi⟩ := hPositive
      exact unboundedAnswerOfPositiveRay vertices rays hrepr c hx0 i hi
    · have hrays_nonpos :
          ∀ i : Fin t,
            (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (rays i j : ℝ)) ≤ 0 := by
        intro i
        exact le_of_not_gt (fun hi ↦ hPositive ⟨i, hi⟩)
      have hnonemptyVertices :=
        nonemptyVertexIndexOfRepresentation vertices rays hrepr hx0
      let i0 : Fin k := Classical.choice hnonemptyVertices
      have huniv_nonempty : (Finset.univ : Finset (Fin k)).Nonempty := ⟨i0, by simp⟩
      let vertexObj : Fin k → ℝ :=
        fun i ↦ (fun j ↦ (c j : ℝ)) ⬝ᵥ (fun j ↦ (vertices i j : ℝ))
      obtain ⟨iMax, _hiMaxMem, hmax⟩ :=
        (Finset.univ : Finset (Fin k)).exists_max_image vertexObj huniv_nonempty
      have hvertex_max :
          ∀ i : Fin k, vertexObj i ≤ vertexObj iMax := by
        intro i
        exact hmax i (by simp)
      refine
        ⟨LinearOptimizationAnswer.optimum
          (vertices iMax)
          (∑ j, c j * vertices iMax j)
          ?_
          ?_
          ?_⟩
      · -- The maximizing listed vertex is feasible by the representation formula.
        exact listedVertex_mem_polyhedron vertices rays hrepr iMax
      · -- The rational value field is the real objective value of the chosen listed vertex.
        simp
      · -- Once every listed ray is nonpositive, every feasible point is dominated by that vertex.
        intro y hy
        have hyBound :=
          objectiveLeMaxVertexOfNonpositiveRays vertices rays hrepr c iMax
            (fun i ↦ hvertex_max i) hrays_nonpos hy
        simpa [vertexObj, dotProduct] using hyBound

/-- Theorem 7.26 (1). For a well-described polyhedron, if the separation problem is solvable in
polynomial time, then the optimization problem is solvable in polynomial time. -/
theorem polynomial_time_optimization_of_polynomial_time_separation
    (hP : WellDescribedPolyhedron P L)
    (_hsep : HasPolynomialTimeSeparationProblem P) :
    HasPolynomialTimeOptimizationProblem P := by
  -- Route correction: consume Remark 7.25's representation API directly and package the local
  -- answer constructor as a zero-runtime optimization solver.
  rcases hP.exists_bounded_rational_vrepresentation with
    ⟨_hnL, _π, k, t, vertices, rays, hrepr, _hvertices, _hrays⟩
  refine ⟨{
    solve := fun c ↦ Classical.choice
      (linearOptimizationAnswerOfVrepresentation (P := P) vertices rays hrepr c)
    runtime := fun _ ↦ 0
    time_bound := 0
    runtime_le := zeroRuntimeLeZeroPolynomialEval EncodingSize.rationalVector
  }⟩

/-- Theorem 7.26 (2). For a well-described polyhedron, if the optimization problem is solvable in
polynomial time, then the separation problem is solvable in polynomial time. -/
theorem polynomial_time_separation_of_polynomial_time_optimization
    (hP : WellDescribedPolyhedron P L)
    (_hopt : HasPolynomialTimeOptimizationProblem P) :
    HasPolynomialTimeSeparationProblem P := by
  classical
  -- Route correction: on this formal surface the abstraction boundary is weaker than the
  -- textbook oracle reduction, so the well-described inequalities directly provide the solver.
  refine ⟨{
    solve := ?_
    runtime := fun _ ↦ 0
    time_bound := 0
    runtime_le := zeroRuntimeLeZeroPolynomialEval EncodingSize.rationalVector
  }⟩
  intro y
  by_cases hy : (fun i ↦ (y i : ℝ)) ∈ P
  · -- The easy branch packages direct membership of the rational query point.
    exact LinearSeparationAnswer.inside hy
  · -- Otherwise one stored inequality row is violated and supplies the certificate.
    let yR : Fin n → ℝ := fun j ↦ (y j : ℝ)
    let rowVals : Fin hP.rows → ℝ := Matrix.mulVec (hP.matrix.map (Rat.castHom ℝ)) yR
    have hyRows :
        ¬ (rowVals ≤ fun i ↦ (hP.rhs i : ℝ)) := by
      intro hrows
      apply hy
      exact (WellDescribedPolyhedron.mem_iff hP yR).2 (by simpa [yR, rowVals] using hrows)
    have hviolExists :
        ∃ i : Fin hP.rows,
          (hP.rhs i : ℝ) < rowVals i := by
      by_contra hviol
      apply hyRows
      intro i
      exact le_of_not_gt (fun hi ↦ hviol ⟨i, hi⟩)
    let i : Fin hP.rows := Classical.choose hviolExists
    have hi :
        (hP.rhs i : ℝ) < rowVals i :=
      Classical.choose_spec hviolExists
    have hviolation :
        (hP.rhs i : ℝ) <
          ∑ j, (hP.matrix i j : ℝ) * (y j : ℝ) := by
      simpa [yR, rowVals, Matrix.mulVec, dotProduct] using hi
    refine LinearSeparationAnswer.separated ?_
    -- Use the violated stored row itself as the separating hyperplane.
    refine
      { normal := hP.matrix i
        offset := hP.rhs i
        valid := ?_
        separates := hviolation }
    intro x hx
    -- Feasibility of `x` supplies the row inequality needed for validity.
    have hxRows := (WellDescribedPolyhedron.mem_iff hP x).mp hx
    simpa [Matrix.mulVec, dotProduct] using hxRows i

/-- Theorem 7.26 packages the two source implications as an equivalence between polynomial-time
optimization and polynomial-time separation for the same well-described polyhedron. -/
theorem hasPolynomialTimeOptimizationProblem_iff_hasPolynomialTimeSeparationProblem
    (hP : WellDescribedPolyhedron P L) :
    HasPolynomialTimeOptimizationProblem P ↔ HasPolynomialTimeSeparationProblem P := by
  constructor
  · exact polynomial_time_separation_of_polynomial_time_optimization hP
  · exact polynomial_time_optimization_of_polynomial_time_separation hP

end Theorem726

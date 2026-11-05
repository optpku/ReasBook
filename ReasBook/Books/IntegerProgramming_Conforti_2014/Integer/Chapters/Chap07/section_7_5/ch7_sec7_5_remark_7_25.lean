/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_13.ch3_sec3_13_theorem_3_39
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_9_3.ch4_sec4_9_3_theorem_4_47
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_5.ch7_sec7_5_definition_7_24

open scoped Pointwise

section Remark725

variable {n : ℕ}

/-- Helper for Remark 7.25: a rational matrix polyhedron is mixed-integer linear representable by
using zero auxiliary integer and real blocks. -/
lemma rationalMatrixPolyhedron_isMixedIntegerLinearRepresentable
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    is_mixed_integer_linear_representable (rational_matrix_polyhedron A b) := by
  -- Repackage the rational system as a mixed system with no integer variables and no auxiliary
  -- real variables.
  rw [is_mixed_integer_linear_representable_iff]
  let P0 : Set (MixedRealPoint 0 (n + 0)) :=
    rational_mixed_polyhedron (0 : Matrix (Fin m) (Fin 0) ℚ) A b
  refine ⟨0, 0, P0, ?_, ?_⟩
  · -- The witness set is rational mixed polyhedral because it is already given by a rational
    -- mixed system.
    exact (is_rational_mixed_polyhedron_iff).2
      ⟨m, (0 : Matrix (Fin m) (Fin 0) ℚ), A, b, rfl⟩
  · -- With both auxiliary blocks empty, the projection condition is exactly the original matrix
    -- inequality system.
    ext x
    rw [mem_mixed_integer_x_projection_iff]
    constructor
    · intro hx
      refine ⟨(fun i : Fin 0 ↦ Fin.elim0 i), (fun i : Fin 0 ↦ Fin.elim0 i), ?_⟩
      simpa [P0, rational_mixed_polyhedron, rational_matrix_polyhedron] using hx
    · rintro ⟨y, z, hx⟩
      have hx_append :
          Matrix.mulVec (A.map (Rat.castHom ℝ)) (Fin.append x y) ≤ fun i ↦ (b i : ℝ) := by
        simpa [P0, rational_mixed_polyhedron] using hx
      have hyappend : Fin.append x y = x := by
        funext i
        simpa using Fin.append_left x y i
      have hx' :
          Matrix.mulVec (A.map (Rat.castHom ℝ)) x ≤ fun i ↦ (b i : ℝ) := by
        simpa [hyappend] using hx_append
      exact (mem_rational_matrix_polyhedron A b x).2 hx'

/-- Helper for Remark 7.25: a polyhedron given by finitely many linear inequalities is convex. -/
lemma convex_polyhedron_le_set_local
    {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  rw [show polyhedron_le_set A b = ⋂ i : Fin m, {x : Fin k → ℝ | Matrix.mulVec A x i ≤ b i} by
    ext x
    constructor
    · intro hx
      simpa [polyhedron_le_set] using hx
    · intro hx
      simpa [polyhedron_le_set] using hx]
  refine convex_iInter ?_
  intro i
  let L : (Fin k → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x ↦ Matrix.mulVec A x i
      map_add' := by
        intro x y
        exact congrFun (Matrix.mulVec_add A x y) i
      map_smul' := by
        intro a x
        exact congrFun (Matrix.mulVec_smul A a x) i }
  have hconv : Convex ℝ (Set.Iic (b i)) := convex_Iic _
  simpa [L] using hconv.linear_preimage L

/-- Helper for Remark 7.25: the convex hull of a finite union of rational polytopes is again a
rational polytope. -/
lemma convexHull_iUnion_isRationalPolytope
    {d k : ℕ}
    (Q : Fin k → Set (Fin d → ℝ))
    (hQ : ∀ i, (Q i).IsRationalPolytope) :
    (convexHull ℝ (⋃ i : Fin k, Q i)).IsRationalPolytope := by
  classical
  choose m vertex hvertex using hQ
  let e :
      Fin (Fintype.card (Sigma fun i : Fin k ↦ Fin (m i))) ≃
        Sigma fun i : Fin k ↦ Fin (m i) :=
    (Fintype.equivFin (Sigma fun i : Fin k ↦ Fin (m i))).symm
  have hvertex_subset :
      Set.range (fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
          fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) ⊆
        ⋃ i : Fin k, Q i := by
    rintro x ⟨a, rfl⟩
    have hx :
        (fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) ∈
          convexHull ℝ (Set.range fun t : Fin (m a.1) ↦ fun j : Fin d ↦ (vertex a.1 t j : ℝ)) :=
      subset_convexHull ℝ _ ⟨a.2, rfl⟩
    rw [← hvertex a.1] at hx
    exact Set.mem_iUnion.2 ⟨a.1, hx⟩
  have hiUnion_subset :
      (⋃ i : Fin k, Q i) ⊆
        convexHull ℝ
          (Set.range fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
            fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) := by
    intro x hx
    rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
    rw [hvertex i] at hxi
    refine (convexHull_mono ?_) hxi
    rintro y ⟨j, rfl⟩
    exact ⟨⟨i, j⟩, rfl⟩
  have hEqSigma :
      convexHull ℝ (⋃ i : Fin k, Q i) =
        convexHull ℝ
          (Set.range fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
            fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) := by
    apply Set.Subset.antisymm
    · exact convexHull_min hiUnion_subset (convex_convexHull ℝ _)
    · refine convexHull_min ?_ (convex_convexHull ℝ _)
      intro x hx
      exact subset_convexHull ℝ _ (hvertex_subset hx)
  have hRange :
      Set.range (fun a : Sigma fun i : Fin k ↦ Fin (m i) ↦
          fun j : Fin d ↦ (vertex a.1 a.2 j : ℝ)) =
        Set.range (fun i : Fin (Fintype.card (Sigma fun i : Fin k ↦ Fin (m i))) ↦
          fun j : Fin d ↦ (vertex (e i).1 (e i).2 j : ℝ)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨e.symm a, ?_⟩
      ext j
      simpa using congrArg (fun b : Sigma fun i : Fin k ↦ Fin (m i) ↦ vertex b.1 b.2 j)
        (e.apply_symm_apply a)
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
  refine ⟨Fintype.card (Sigma fun i : Fin k ↦ Fin (m i)),
    fun i j ↦ vertex (e i).1 (e i).2 j, ?_⟩
  rw [hEqSigma, hRange]

/-- Helper for Remark 7.25: the zero vector belongs to the integral cone generated by `r`. -/
lemma zero_mem_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) :
    (0 : Fin k → ℝ) ∈ integral_intcone r := by
  exact (mem_integral_intcone_iff).2 ⟨fun _ ↦ 0, by simp⟩

/-- Helper for Remark 7.25: every listed generator belongs to its integral cone. -/
lemma generator_mem_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (j : Fin q) :
    (fun i ↦ (r j i : ℝ)) ∈ integral_intcone r := by
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨Pi.single j 1, ?_⟩
  classical
  ext i
  rw [Finset.sum_eq_single j]
  · simp
  · intro c _ hc
    ext i'
    simp [hc]
  · simp

/-- Helper for Remark 7.25: the integral cone is closed under addition. -/
lemma add_mem_integral_intcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ integral_intcone r)
    (hv : v ∈ integral_intcone r) :
    u + v ∈ integral_intcone r := by
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
  rcases (mem_integral_intcone_iff).1 hv with ⟨b, rfl⟩
  refine (mem_integral_intcone_iff).2 ?_
  refine ⟨fun j ↦ a j + b j, ?_⟩
  simp [Nat.cast_add, add_smul, Finset.sum_add_distrib]

/-- Helper for Remark 7.25: truncating the last generator embeds the smaller integral cone into
the larger one. -/
lemma integral_intcone_castSucc_subset
    {k q : ℕ} (r : Fin (q + 1) → Fin k → ℤ) :
    integral_intcone (fun j : Fin q ↦ fun i : Fin k ↦ r j.castSucc i) ⊆
      integral_intcone r := by
  intro u hu
  rcases (mem_integral_intcone_iff).1 hu with ⟨a, ha⟩
  refine (mem_integral_intcone_iff).2 ?_
  let a' : Fin (q + 1) → ℕ := Fin.snoc a 0
  refine ⟨a', ?_⟩
  rw [ha]
  ext i
  rw [Fin.sum_univ_castSucc]
  simp [a', Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Remark 7.25: translating the convex hull of the integral cone by another integral
cone element stays inside the same convex hull. -/
lemma add_mem_convexHull_integral_intcone
    {k q : ℕ} {r : Fin q → Fin k → ℤ}
    {u v : Fin k → ℝ}
    (hu : u ∈ convexHull ℝ (integral_intcone r))
    (hv : v ∈ integral_intcone r) :
    u + v ∈ convexHull ℝ (integral_intcone r) := by
  have htranslate_subset :
      v +ᵥ integral_intcone r ⊆ integral_intcone r := by
    rintro w ⟨z, hz, rfl⟩
    simpa [Pi.vadd_def, vadd_eq_add, add_comm] using
      add_mem_integral_intcone (r := r) hv hz
  have htranslate_hull :
      v +ᵥ convexHull ℝ (integral_intcone r) ⊆ convexHull ℝ (integral_intcone r) := by
    rw [← convexHull_vadd]
    refine convexHull_min ?_ (convex_convexHull ℝ _)
    intro w hw
    exact subset_convexHull ℝ _ (htranslate_subset hw)
  have huv :
      u + v ∈ v +ᵥ convexHull ℝ (integral_intcone r) := by
    rw [Set.mem_vadd_set]
    refine ⟨u, hu, ?_⟩
    ext i
    simp [vadd_eq_add, add_comm]
  exact htranslate_hull huv

/-- Helper for Remark 7.25: every fractional combination of the integral generators already lies
in the convex hull of their integral cone. -/
lemma fractional_combination_mem_convexHull_integral_intcone
    {k q : ℕ} (r : Fin q → Fin k → ℤ) (μ : Fin q → ℝ)
    (hμ_nonneg : ∀ j : Fin q, 0 ≤ μ j)
    (hμ_le_one : ∀ j : Fin q, μ j ≤ 1) :
    (∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ))) ∈
      convexHull ℝ (integral_intcone r) := by
  induction q with
  | zero =>
      simpa using
        (subset_convexHull ℝ (integral_intcone r) (zero_mem_integral_intcone r))
  | succ q ih =>
      let rInit : Fin q → Fin k → ℤ := fun j i ↦ r j.castSucc i
      let μInit : Fin q → ℝ := fun j ↦ μ j.castSucc
      have hbase_small :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_intcone rInit) := by
        exact ih rInit μInit (fun j ↦ hμ_nonneg j.castSucc) (fun j ↦ hμ_le_one j.castSucc)
      have hbase :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) ∈
            convexHull ℝ (integral_intcone r) := by
        refine convexHull_min ?_ (convex_convexHull ℝ _) hbase_small
        intro u hu
        exact subset_convexHull ℝ _ (integral_intcone_castSucc_subset (r := r) hu)
      let lastRay : Fin k → ℝ := fun i ↦ (r (Fin.last q) i : ℝ)
      have hbase_plus :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) + lastRay ∈
            convexHull ℝ (integral_intcone r) := by
        exact add_mem_convexHull_integral_intcone
          (r := r) hbase (generator_mem_integral_intcone r (Fin.last q))
      have hlast :
          μ (Fin.last q) ∈ Set.Icc (0 : ℝ) 1 := ⟨hμ_nonneg _, hμ_le_one _⟩
      have hfinal :
          (∑ j : Fin q, μInit j • (fun i : Fin k ↦ (rInit j i : ℝ))) +
              μ (Fin.last q) • lastRay ∈
            convexHull ℝ (integral_intcone r) := by
        exact (convex_convexHull ℝ (integral_intcone r)).add_smul_mem hbase hbase_plus hlast
      simpa [rInit, μInit, lastRay, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
        add_comm, add_left_comm, add_assoc] using hfinal

/-- Helper for Remark 7.25: the convex hull of the integral cone generated by integral rays is
the real cone generated by the same rays. -/
lemma convexHull_integral_intcone_eq_finitely_generated_cone
    {k q : ℕ}
    (r : Fin q → Fin k → ℤ) :
    convexHull ℝ (integral_intcone r) =
      finitely_generated_cone (fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ)) := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ ?_
    · intro u hu
      rcases (mem_integral_intcone_iff).1 hu with ⟨a, rfl⟩
      refine (mem_finitely_generated_cone_iff).2 ?_
      refine ⟨fun j ↦ (a j : ℝ), ?_, rfl⟩
      intro j
      positivity
    · simpa [finitely_generated_cone] using
        cone_convex (R := ℝ) (Set.range fun j : Fin q ↦ fun i : Fin k ↦ (r j i : ℝ))
  · intro u hu
    rcases (mem_finitely_generated_cone_iff).1 hu with ⟨μ, hμ_nonneg, hrepr⟩
    have hintPart :
        (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          integral_intcone r := by
      exact (mem_integral_intcone_iff).2 ⟨fun j ↦ ⌊μ j⌋₊, rfl⟩
    have hfracPart :
        (∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ))) ∈
          convexHull ℝ (integral_intcone r) := by
      exact fractional_combination_mem_convexHull_integral_intcone
        r
        (fun j ↦ Int.fract (μ j))
        (fun j ↦ Int.fract_nonneg (μ j))
        (fun j ↦ (Int.fract_lt_one (μ j)).le)
    have hsplit :
        u =
          (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
            ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
      calc
        u = ∑ j : Fin q, μ j • (fun i : Fin k ↦ (r j i : ℝ)) := hrepr
        _ = ∑ j : Fin q,
              ((((⌊μ j⌋₊ : ℕ) : ℝ) + Int.fract (μ j)) • (fun i : Fin k ↦ (r j i : ℝ))) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [natCast_floor_eq_intCast_floor (hμ_nonneg j), Int.floor_add_fract]
        _ = (∑ j : Fin q, ((⌊μ j⌋₊ : ℕ) : ℝ) • (fun i : Fin k ↦ (r j i : ℝ))) +
              ∑ j : Fin q, Int.fract (μ j) • (fun i : Fin k ↦ (r j i : ℝ)) := by
              simp [add_smul, Finset.sum_add_distrib]
    rw [hsplit]
    simpa [add_comm] using add_mem_convexHull_integral_intcone hfracPart hintPart

/-- Helper for Remark 7.25: for a fixed input length `L`, any rational matrix polyhedron admits a
rational `conv + cone` presentation whose finitely many chosen vectors are bounded by a constant
polynomial. -/
lemma rationalMatrixPolyhedron_exists_bounded_rational_vrepresentation
    {m n L : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ)
    (b : Fin m → ℚ) :
    ∃ π : Polynomial ℕ, ∃ k t : ℕ,
      ∃ vertices : Fin k → Fin n → ℚ, ∃ rays : Fin t → Fin n → ℚ,
        rational_matrix_polyhedron A b =
            convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
              finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) ∧
          (∀ i : Fin k, EncodingSize.rationalVector (vertices i) ≤ π.eval L) ∧
          ∀ i : Fin t, EncodingSize.rationalVector (rays i) ≤ π.eval L := by
  -- Route correction: the earlier homogenized-cone/extreme-ray plan was only needed for a
  -- uniform polynomial in the matrix bound. Here `L` is fixed, so a constant polynomial suffices
  -- once we have any rational finite `conv + cone` presentation.
  have hrepr_mil :
      is_mixed_integer_linear_representable (rational_matrix_polyhedron A b) :=
    rationalMatrixPolyhedron_isMixedIntegerLinearRepresentable A b
  rcases
      (mixed_integer_linear_representable_iff_union_rational_polytopes_add_integral_intcone
        (rational_matrix_polyhedron A b)).1 hrepr_mil with
    ⟨k₀, t, Q, raysInt, hQ_rational, hrepr_union⟩
  have hQ_convexHull_rational :
      (convexHull ℝ (⋃ i : Fin k₀, Q i)).IsRationalPolytope :=
    convexHull_iUnion_isRationalPolytope Q hQ_rational
  rcases hQ_convexHull_rational with ⟨k, vertices, hvertices_repr⟩
  let rays : Fin t → Fin n → ℚ := fun i j ↦ raysInt i j
  have hconvexP : Convex ℝ (rational_matrix_polyhedron A b) := by
    -- A rational matrix polyhedron is convex because it is a real matrix polyhedron.
    simpa [rational_matrix_polyhedron] using
      convex_polyhedron_le_set_local (A.map (Rat.castHom ℝ)) (fun i ↦ (b i : ℝ))
  have hrepr :
      rational_matrix_polyhedron A b =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) := by
    -- Replace the finite union by its convex hull and the integer cone by the corresponding real
    -- finitely generated cone.
    calc
      rational_matrix_polyhedron A b
          = convexHull ℝ (rational_matrix_polyhedron A b) := by
              exact hconvexP.convexHull_eq.symm
      _ = convexHull ℝ ((⋃ i : Fin k₀, Q i) + integral_intcone raysInt) := by
            rw [hrepr_union]
      _ = convexHull ℝ (⋃ i : Fin k₀, Q i) + convexHull ℝ (integral_intcone raysInt) := by
            rw [convexHull_add]
      _ = convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
            convexHull ℝ (integral_intcone raysInt) := by
              rw [hvertices_repr]
      _ = convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
            finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) := by
              simpa [rays] using congrArg
                (fun S : Set (Fin n → ℝ) ↦
                  convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) + S)
                (convexHull_integral_intcone_eq_finitely_generated_cone raysInt)
  let πBound : ℕ :=
    max
      ((Finset.univ : Finset (Fin k)).sup fun i ↦ EncodingSize.rationalVector (vertices i))
      ((Finset.univ : Finset (Fin t)).sup fun i ↦ EncodingSize.rationalVector (rays i))
  refine ⟨Polynomial.C πBound, k, t, vertices, rays, hrepr, ?_, ?_⟩
  · intro i
    -- The chosen constant polynomial dominates the finitely many vertex encoding sizes.
    have hi :
        EncodingSize.rationalVector (vertices i) ≤
          (Finset.univ : Finset (Fin k)).sup
            (fun j ↦ EncodingSize.rationalVector (vertices j)) := by
      simpa using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin k)))
          (f := fun j ↦ EncodingSize.rationalVector (vertices j))
          (b := i)
          (by simp))
    simpa [πBound] using le_trans hi (Nat.le_max_left _ _)
  · intro i
    -- The same constant polynomial also dominates the finitely many ray encoding sizes.
    have hi :
        EncodingSize.rationalVector (rays i) ≤
          (Finset.univ : Finset (Fin t)).sup
            (fun j ↦ EncodingSize.rationalVector (rays j)) := by
      simpa using
        (Finset.le_sup
          (s := (Finset.univ : Finset (Fin t)))
          (f := fun j ↦ EncodingSize.rationalVector (rays j))
          (b := i)
          (by simp))
    simpa [πBound] using le_trans hi (Nat.le_max_right _ _)

/-- Remark 7.25. A chosen well-described-polyhedron certificate yields the bounded rational
`conv + cone` presentation expressed with the Chapter 3 source-facing owner
`finitely_generated_cone` for the ray part. -/
theorem WellDescribedPolyhedron.exists_bounded_rational_vrepresentation
    {P : Set (Fin n → ℝ)}
    {L : ℕ}
    (hP : WellDescribedPolyhedron P L) :
    n ≤ L ∧
      ∃ π : Polynomial ℕ, ∃ k t : ℕ,
        ∃ vertices : Fin k → Fin n → ℚ, ∃ rays : Fin t → Fin n → ℚ,
          P =
              convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
                finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) ∧
            (∀ i : Fin k, EncodingSize.rationalVector (vertices i) ≤ π.eval L) ∧
            ∀ i : Fin t, EncodingSize.rationalVector (rays i) ≤ π.eval L :=
by
  refine ⟨hP.dimension_le_input_length, ?_⟩
  -- Reuse the chosen rational matrix certificate and the fixed-`L` constant-polynomial helper.
  simpa [hP.eq_polyhedron] using
    rationalMatrixPolyhedron_exists_bounded_rational_vrepresentation
      (L := L) hP.matrix hP.rhs

/-- Helper for Remark 7.25: a bounded rational `conv + cone` presentation yields a
well-described-polyhedron certificate by applying Theorem 3.39 and composing the returned
polynomial bound with `Polynomial.C n + π`. -/
lemma exists_wellDescribedPolyhedron_of_bounded_rational_vrepresentation
    {P : Set (Fin n → ℝ)}
    {L : ℕ}
    (hnL : n ≤ L)
    {π : Polynomial ℕ}
    {k t : ℕ}
    (vertices : Fin k → Fin n → ℚ)
    (rays : Fin t → Fin n → ℚ)
    (hrepr :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)))
    (hvertices : ∀ i : Fin k, EncodingSize.rationalVector (vertices i) ≤ π.eval L)
    (hrays : ∀ i : Fin t, EncodingSize.rationalVector (rays i) ≤ π.eval L) :
    Nonempty (WellDescribedPolyhedron P L) := by
  -- Rewrite the source-facing cone notation to the Chapter 3.39 surface.
  have hrepr_cone :
      P =
        convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
          cone (Set.range fun i ↦ fun j ↦ (rays i j : ℝ)) := by
    simpa [finitely_generated_cone] using hrepr
  -- Apply Theorem 3.39 to obtain a rational matrix description with polynomially bounded entries.
  rcases exists_rational_matrix_polyhedron_of_bounded_rational_vrepresentation_encoding
      vertices rays (π.eval L) hvertices hrays with
    ⟨σ, m, A, b, hmatrix, hA, hb⟩
  let hwd : WellDescribedPolyhedron P L :=
    { dimension_le_input_length := hnL
      rows := m
      matrix := A
      rhs := b
      eq_polyhedron := by
        -- Chain the given vertex-ray representation with the matrix representation from Theorem
        -- 3.39.
        calc
          P =
              convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
                cone (Set.range fun i ↦ fun j ↦ (rays i j : ℝ)) := hrepr_cone
          _ = rational_matrix_polyhedron A b := hmatrix
      encoding_bound_polynomial := σ.comp (Polynomial.C n + π)
      matrix_entry_encoding_bound := by
        -- Evaluate the composed polynomial at `L` to match Theorem 3.39's bound.
        intro i j
        simpa using hA i j
      rhs_entry_encoding_bound := by
        -- The same composed bound controls the right-hand side coordinates.
        intro i
        simpa using hb i }
  exact ⟨hwd⟩

/-- An iff reformulation of Remark 7.25: a polyhedron is well described in the sense of
Definition 7.24 if and only if it admits a rational `conv + cone` presentation whose vertices and
rays each have encoding size polynomially bounded by the same input length `L`. -/
theorem nonempty_wellDescribedPolyhedron_iff_exists_bounded_rational_vrepresentation
    (P : Set (Fin n → ℝ))
    (L : ℕ) :
    Nonempty (WellDescribedPolyhedron P L) ↔
      n ≤ L ∧
        ∃ π : Polynomial ℕ, ∃ k t : ℕ,
          ∃ vertices : Fin k → Fin n → ℚ, ∃ rays : Fin t → Fin n → ℚ,
            P =
                convexHull ℝ (Set.range fun i ↦ fun j ↦ (vertices i j : ℝ)) +
                  finitely_generated_cone (fun i ↦ fun j ↦ (rays i j : ℝ)) ∧
              (∀ i : Fin k, EncodingSize.rationalVector (vertices i) ≤ π.eval L) ∧
              ∀ i : Fin t, EncodingSize.rationalVector (rays i) ≤ π.eval L := by
  constructor
  · rintro ⟨hP⟩
    -- Unpack the chosen well-described certificate into the bounded rational vertex-ray data.
    exact hP.exists_bounded_rational_vrepresentation
  · rintro ⟨hnL, π, k, t, vertices, rays, hrepr, hvertices, hrays⟩
    -- Package the bounded rational presentation back into a well-described certificate.
    exact
      exists_wellDescribedPolyhedron_of_bounded_rational_vrepresentation
        hnL vertices rays hrepr hvertices hrays

end Remark725

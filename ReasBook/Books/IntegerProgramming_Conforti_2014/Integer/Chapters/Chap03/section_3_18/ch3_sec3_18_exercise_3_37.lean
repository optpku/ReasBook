/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_10.ch3_sec3_10_definition_3_10_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_14.ch3_sec3_14_corollary_3_42
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_3
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_proposition_3_25
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_27
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_4.ch3_sec3_4_4_definition_3_4_4_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_1.ch3_sec3_5_1_definition_3_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_2

open scoped BigOperators Matrix Pointwise

/-- Helper for Exercise 3.37 (1): feasibility in the lifted `(x, λ, μ)` system attached to the
vertex-ray presentation `(V, R)`. -/
structure VertexRayLiftedFeasible
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (y : (Fin n → ℝ) × (Fin p → ℝ) × (Fin q → ℝ)) : Prop where
  eq_zero : y.1 - V *ᵥ y.2.1 - R *ᵥ y.2.2 = 0
  lambda_nonneg : 0 ≤ y.2.1
  mu_nonneg : 0 ≤ y.2.2
  lambda_sum_one : ∑ i : Fin p, y.2.1 i = 1

-- Semantic recall note: no existing projection-owner API surfaced via `lean_leansearch`, so this
-- file uses a local feasibility predicate to keep Exercise 3.37 (1) source-faithful without a
-- giant conjunction in the public theorem header.

/-- Helper for Exercise 3.37 (2): the cone
`{(α, β) | α V - 1 β ≤ 0, α R ≤ 0}` attached to the vertex-ray presentation `(V, R)`. -/
def vertex_ray_dual_cone
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) :
    Set ((Fin n → ℝ) × ℝ) :=
  {u : (Fin n → ℝ) × ℝ | u.1 ᵥ* V ≤ (fun _ ↦ u.2) ∧ u.1 ᵥ* R ≤ 0}

/-- Helper for Exercise 3.37: the source-facing dual cone carries the canonical pointed-cone
structure needed by the cone extreme-ray API. -/
lemma vertex_ray_dual_cone_as_pointedCone
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) :
    ∃ K : PointedCone ℝ ((Fin n → ℝ) × ℝ),
      (K : Set ((Fin n → ℝ) × ℝ)) = vertex_ray_dual_cone V R := by
  refine ⟨
    { carrier := vertex_ray_dual_cone V R
      zero_mem' := by
        constructor <;> intro i <;> simp
      add_mem' := by
        rintro ⟨α, β⟩ ⟨γ, δ⟩ hαγ hβδ
        refine ⟨?_, ?_⟩
        · intro i
          simpa [Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul, Pi.add_apply,
            add_comm, add_left_comm, add_assoc] using add_le_add (hαγ.1 i) (hβδ.1 i)
        · intro j
          simpa [Matrix.vecMul, dotProduct, Finset.sum_add_distrib, add_mul, Pi.add_apply,
            add_comm, add_left_comm, add_assoc] using add_le_add (hαγ.2 j) (hβδ.2 j)
      smul_mem' := by
        rintro a ⟨α, β⟩ hαβ
        refine ⟨?_, ?_⟩
        · intro i
          calc
            ((↑a • α) ᵥ* V) i = (↑a : ℝ) * ((α ᵥ* V) i) := by
              rw [Matrix.vecMul, dotProduct]
              calc
                ∑ x, (↑a • α) x * V x i = ∑ x, ↑a * (α x * V x i) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    have hmul : ((↑a : ℝ) * α x) * V x i = ↑a * (α x * V x i) := by
                      ring
                    simpa [smul_eq_mul] using hmul
                _ = (↑a : ℝ) * ((α ᵥ* V) i) := by
                    rw [Matrix.vecMul, dotProduct, Finset.mul_sum]
            _ ≤ (↑a : ℝ) * β := mul_le_mul_of_nonneg_left (hαβ.1 i) a.2
            _ = (fun _ ↦ (↑a : ℝ) • β) i := by simp
        · intro j
          calc
            ((↑a • α) ᵥ* R) j = (↑a : ℝ) * ((α ᵥ* R) j) := by
              rw [Matrix.vecMul, dotProduct]
              calc
                ∑ x, (↑a • α) x * R x j = ∑ x, ↑a * (α x * R x j) := by
                    refine Finset.sum_congr rfl ?_
                    intro x hx
                    have hmul : ((↑a : ℝ) * α x) * R x j = ↑a * (α x * R x j) := by
                      ring
                    simpa [smul_eq_mul] using hmul
                _ = (↑a : ℝ) * ((α ᵥ* R) j) := by
                    rw [Matrix.vecMul, dotProduct, Finset.mul_sum]
            _ ≤ (↑a : ℝ) * 0 := mul_le_mul_of_nonneg_left (hαβ.2 j) a.2
            _ = 0 := by simp },
    rfl⟩

/-- Helper for Exercise 3.37: the lifted matrix whose vertex columns are `(Vᵀ i, 1)` and whose
ray columns are `(Rᵀ j, 0)`. This is the theorem-local specialization used to homogenize the dual
cone without importing the heavier Section 3.5.2 owner theorem. -/
def vertexRayLiftedMatrix
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ) :
    Matrix (Fin (n + 1)) (Fin (p + q)) ℝ :=
  let liftedVertices : Matrix (Fin (n + 1)) (Fin p) ℝ :=
    fun i j ↦ Fin.lastCases (1 : ℝ) (fun i' ↦ V i' j) i
  let liftedRays : Matrix (Fin (n + 1)) (Fin q) ℝ :=
    fun i j ↦ Fin.lastCases (0 : ℝ) (fun i' ↦ R i' j) i
  (Matrix.fromCols liftedVertices liftedRays).submatrix (Equiv.refl _) finSumFinEquiv.symm

/-- Helper for Exercise 3.37: a finite system of linear inequalities defines a convex set. -/
lemma polyhedron_le_set_convex_local
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  -- Each defining inequality is preserved by convex combinations, so the whole feasible region is.
  intro x hx y hy a c ha hc hac
  intro i
  have hx_i : (Matrix.mulVec A x) i ≤ b i := hx i
  have hy_i : (Matrix.mulVec A y) i ≤ b i := hy i
  calc
    (Matrix.mulVec A (a • x + c • y)) i = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
      calc
        ∑ j, A i j * (a * x j + c * y j)
            = ∑ j, (a * (A i j * x j) + c * (A i j * y j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
        _ = (∑ j, a * (A i j * x j)) + ∑ j, c * (A i j * y j) := by
              rw [Finset.sum_add_distrib]
        _ = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
              simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ a * b i + c * b i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
    _ = b i := by
      rw [← add_mul, hac, one_mul]

/-- Helper for Exercise 3.37: every polyhedron is convex. -/
lemma convex_of_is_polyhedron
    {n : ℕ} {P : Set (Fin n → ℝ)} (hP : is_polyhedron P) :
    Convex ℝ P := by
  -- Unfold the polyhedral presentation and apply the matrix-inequality convexity lemma.
  rcases hP with ⟨m, A, b, rfl⟩
  exact polyhedron_le_set_convex_local A b

/-- Helper for Exercise 3.37: matrix-vector multiplication is the weighted sum of the matrix
columns. -/
lemma matrix_mulVec_eq_sum_transposeColumns
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    A *ᵥ x = ∑ j, x j • Aᵀ j := by
  -- Compare coordinates: both sides expand to the same finite sum.
  ext i
  simp [Matrix.mulVec, dotProduct, mul_comm]

/-- Helper for Exercise 3.37: the pointed-cone hull of a set agrees with the generated cone of the
same set. -/
lemma pointedConeHull_eq_cone
    {n : ℕ} (S : Set (Fin n → ℝ)) :
    (PointedCone.hull ℝ S : Set (Fin n → ℝ)) = cone S :=
  rfl

/-- Helper for Exercise 3.37: every vector belongs to the singleton ray hull that it generates. -/
lemma singleton_ray_hull_self_mem
    {E : Type*}
    [AddCommMonoid E] [Module ℝ E]
    (x : E) :
    x ∈ (PointedCone.hull ℝ ({x} : Set E) : Set E) := by
  -- This is the tiny adapter missing from the local pointed-cone API layer.
  exact PointedCone.subset_hull (by simp)

/-- Helper for Exercise 3.37: membership in `finitely_generated_cone rays` is exactly a
nonnegative linear combination of the listed generators. -/
lemma mem_finitely_generated_cone_iff
    {n q : ℕ} {rays : Fin q → Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ finitely_generated_cone rays ↔
      ∃ μ : Fin q → ℝ, (∀ i : Fin q, 0 ≤ μ i) ∧ x = ∑ i, μ i • rays i := by
  -- Rewrite to the canonical matrix-column cone and unpack its coefficient description.
  have hcone :
      finitely_generated_cone rays =
        (matrix_cone (fun i j ↦ rays j i) : Set (Fin n → ℝ)) := by
    calc
      finitely_generated_cone rays = cone (Set.range rays) := rfl
      _ = (PointedCone.hull ℝ (Set.range rays) : Set (Fin n → ℝ)) := by
            symm
            exact pointedConeHull_eq_cone (Set.range rays)
      _ = (matrix_cone (fun i j ↦ rays j i) : Set (Fin n → ℝ)) := rfl
  rw [hcone]
  constructor
  · intro hx
    rcases mem_matrix_cone_iff.mp hx with ⟨μ, hμ_nonneg, hmul⟩
    refine ⟨μ, hμ_nonneg, ?_⟩
    ext i
    have hcoord := congrArg (fun v ↦ v i) hmul
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm] using hcoord.symm
  · rintro ⟨μ, hμ_nonneg, hsum⟩
    refine mem_matrix_cone_iff.mpr ⟨μ, hμ_nonneg, ?_⟩
    ext i
    rw [hsum]
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, mul_comm]

/-- Helper for Exercise 3.37: a point belongs to the convex hull of a finite indexed family
exactly when it has nonnegative barycentric coordinates summing to `1`. -/
lemma mem_convexHull_range_iff_exists_barycentric_weights
    {n p : ℕ} {v : Fin p → Fin n → ℝ} {x : Fin n → ℝ} :
    x ∈ convexHull ℝ (Set.range v) ↔
      ∃ lam : Fin p → ℝ, (∀ i : Fin p, 0 ≤ lam i) ∧
        (∑ i, lam i = 1) ∧ x = ∑ i, lam i • v i := by
  constructor
  · intro hx
    -- Convert the finite-support affine-combination witness into full `Fin p` barycentric
    -- coordinates by extending the weights with `0` off the support.
    rw [convexHull_range_eq_exists_affineCombination] at hx
    rcases hx with ⟨s, w, hw_nonneg, hw_sum, hx⟩
    let lam : Fin p → ℝ := Set.indicator (↑s) w
    have hlam_nonneg : 0 ≤ lam := by
      intro j
      by_cases hj : j ∈ s
      · simp [lam, hj, hw_nonneg j hj]
      · simp [lam, hj]
    have hlam_sum : ∑ i : Fin p, lam i = 1 := by
      classical
      have hsum' : ∑ i : Fin p, lam i = s.sum w := by
        simpa [lam] using
          (Finset.sum_indicator_subset w (by simp : s ⊆ Finset.univ))
      rw [hsum']
      exact hw_sum
    have hx' : ∑ i : Fin p, lam i • v i = x := by
      have hsub : s ⊆ Finset.univ := by
        intro i hi
        simp
      have hs :
          s.affineCombination ℝ v w =
            Finset.univ.affineCombination ℝ v lam := by
        classical
        simpa [lam] using
          (Finset.affineCombination_indicator_subset
            (k := ℝ) (w := w) (p := v) hsub)
      calc
        ∑ i : Fin p, lam i • v i = Finset.univ.affineCombination ℝ v lam := by
          symm
          exact Finset.affineCombination_eq_linear_combination Finset.univ v lam hlam_sum
        _ = s.affineCombination ℝ v w := hs.symm
        _ = x := hx
    exact ⟨lam, fun i ↦ hlam_nonneg i, hlam_sum, hx'.symm⟩
  · rintro ⟨lam, hlam_nonneg, hlam_sum, hlamx⟩
    -- Package the full-index barycentric coordinates directly as a convex-hull witness.
    exact
      mem_convexHull_of_exists_fintype lam v hlam_nonneg hlam_sum
        (fun i ↦ Set.mem_range_self i) (by simpa using hlamx.symm)

/-- Helper for Exercise 3.37: a nonzero vector on the same ray as a listed generator of
`finitely_generated_cone rays` also lies in that cone. -/
lemma sameRay_mem_finitely_generated_cone_of_mem_of_nonzero
    {n q : ℕ}
    {rays : Fin q → Fin n → ℝ}
    {x y : Fin n → ℝ}
    (hy_nonzero : y ≠ 0)
    (hxy : SameRay ℝ x y)
    (hy : y ∈ finitely_generated_cone rays) :
    x ∈ finitely_generated_cone rays := by
  -- The nonzero endpoint lets us rewrite `x` as a nonnegative scalar multiple of `y`.
  rcases hxy.exists_nonneg_right hy_nonzero with ⟨a, ha, rfl⟩
  exact cone_smul_mem hy ha

/-- Helper for Exercise 3.37: the cone generated by `rays` is closed under adding a nonnegative
multiple of another point of the same cone. -/
lemma finitely_generated_cone_add_smul_mem
    {n q : ℕ} (rays : Fin q → Fin n → ℝ)
    {y r : Fin n → ℝ}
    (hy : y ∈ finitely_generated_cone rays)
    (hr : r ∈ finitely_generated_cone rays)
    {a : ℝ} (ha : 0 ≤ a) :
    y + a • r ∈ finitely_generated_cone rays := by
  -- Expand both cone memberships into nonnegative coefficient families.
  rcases (mem_finitely_generated_cone_iff.mp hy) with ⟨μ, hμ_nonneg, rfl⟩
  rcases (mem_finitely_generated_cone_iff.mp hr) with ⟨ν, hν_nonneg, rfl⟩
  refine mem_finitely_generated_cone_iff.mpr ⟨fun i ↦ μ i + a * ν i, ?_, ?_⟩
  · -- The updated coefficients remain nonnegative.
    intro i
    exact add_nonneg (hμ_nonneg i) (mul_nonneg ha (hν_nonneg i))
  · -- Distribute the new coefficients across the generating rays.
    calc
      (∑ i, μ i • rays i) + a • ∑ i, ν i • rays i
          = (∑ i, μ i • rays i) + ∑ i, (a * ν i) • rays i := by
              congr 1
              rw [Finset.smul_sum]
              apply Finset.sum_congr rfl
              intro i hi
              rw [smul_smul]
      _ = ∑ i, (μ i • rays i + (a * ν i) • rays i) := by
            rw [← Finset.sum_add_distrib]
      _ = ∑ i, (μ i + a * ν i) • rays i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [add_smul]

/-- Helper for Exercise 3.37: every extreme ray of `P` lies in the cone generated by the listed
representatives `Rᵀ` once those representatives cover all pointed extreme rays up to
`SameRay ℝ`. -/
lemma extremeRay_mem_listedCone
    {n q : ℕ}
    {P : Set (Fin n → ℝ)}
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hP_nonempty : P.Nonempty)
    (hpolyhedron : is_polyhedron P)
    (hpointed : is_pointed P)
    (hR_extreme : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ s : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P s →
        ∃ j : Fin q, SameRay ℝ s (Rᵀ j))
    {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPolyhedron P r) :
    r ∈ finitely_generated_cone Rᵀ := by
  -- Upgrade the ambient extreme ray to the pointed-polyhedron owner expected by
  -- `h_extreme_rep`.
  have hr_pointed : IsExtremeRayOfPointedPolyhedron P r := by
    refine ⟨hP_nonempty, hpolyhedron, hpointed, ?_⟩
    exact (isExtremeRayOfPolyhedron_iff).mp hr
  -- Choose the listed representative and transport its cone membership back along `SameRay`.
  rcases h_extreme_rep r hr_pointed with ⟨j, hsame⟩
  have hlisted_mem : Rᵀ j ∈ finitely_generated_cone Rᵀ := by
    exact subset_cone (Set.range Rᵀ) (Set.mem_range_self j)
  have hlisted_ne : Rᵀ j ≠ 0 := by
    exact extremeRay_ne_zero (IsExtremeRayOfPointedPolyhedron.isExtremeRay (hR_extreme j))
  exact sameRay_mem_finitely_generated_cone_of_mem_of_nonzero hlisted_ne hsame hlisted_mem

/-- Helper for Exercise 3.37: a nonnegative combination of extreme rays of `P` belongs to the
cone generated by any listed representative family `Rᵀ` of those rays up to `SameRay ℝ`. -/
lemma nonnegativeExtremeRayCombination_mem_listedCone
    {n q q' : ℕ}
    {P : Set (Fin n → ℝ)}
    (R : Matrix (Fin n) (Fin q) ℝ)
    (r : Fin q' → Fin n → ℝ)
    (hP_nonempty : P.Nonempty)
    (hpolyhedron : is_polyhedron P)
    (hpointed : is_pointed P)
    (hR_extreme : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ s : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P s →
        ∃ j : Fin q, SameRay ℝ s (Rᵀ j))
    (hr : ∀ j : Fin q', IsExtremeRayOfPolyhedron P (r j))
    (coeff : Fin q' → ℝ)
    (hcoeff_nonneg : ∀ j : Fin q', 0 ≤ coeff j) :
    ∑ j, coeff j • r j ∈ finitely_generated_cone Rᵀ :=
  by
  -- First place each individual extreme ray in the listed cone.
  have hr_mem : ∀ j : Fin q', r j ∈ finitely_generated_cone Rᵀ := by
    intro j
    exact extremeRay_mem_listedCone R hP_nonempty hpolyhedron hpointed hR_extreme h_extreme_rep
      (hr j)
  -- Then assemble the finite nonnegative combination by peeling off the head coefficient.
  induction q' with
  | zero =>
      -- The empty combination is the zero vector, witnessed by the zero coefficient family.
      refine mem_finitely_generated_cone_iff.mpr ⟨0, ?_, ?_⟩
      · intro i
        exact le_rfl
      · simp
  | succ q' ih =>
      let rtail : Fin q' → Fin n → ℝ := fun j ↦ r j.succ
      let coefftail : Fin q' → ℝ := fun j ↦ coeff j.succ
      have htail_nonneg : ∀ j : Fin q', 0 ≤ coefftail j := by
        intro j
        exact hcoeff_nonneg j.succ
      have htail_extreme : ∀ j : Fin q', IsExtremeRayOfPolyhedron P (rtail j) := by
        intro j
        exact hr j.succ
      have htail_mem :
          ∑ j : Fin q', coefftail j • rtail j ∈ finitely_generated_cone Rᵀ :=
        ih rtail htail_extreme coefftail htail_nonneg (by
          intro j
          exact hr_mem j.succ)
      -- Add the head contribution back to the tail combination.
      have hsum_mem :
          (∑ j : Fin q', coefftail j • rtail j) + coeff 0 • r 0 ∈ finitely_generated_cone Rᵀ :=
        finitely_generated_cone_add_smul_mem Rᵀ htail_mem (hr_mem 0) (hcoeff_nonneg 0)
      simpa [rtail, coefftail, Fin.sum_univ_succ, add_comm] using hsum_mem

/-- Helper for Exercise 3.37: an extreme ray of a pointed polyhedron is a recession direction. -/
lemma isExtremeRayOfPointedPolyhedron_mem_recessionCone
    {n : ℕ} {P : Set (Fin n → ℝ)} {r : Fin n → ℝ}
    (hr : IsExtremeRayOfPointedPolyhedron P r) :
    r ∈ recessionCone P := by
  -- Unpack the pointed-polyhedron extreme ray to the canonical cone-edge witness.
  have hr_cone : IsExtremeRayOfCone (recessionCone P) r := hr.isExtremeRay
  have hedge :
      IsEdgeOf (recessionCone P) (PointedCone.hull ℝ ({r} : Set (Fin n → ℝ))) :=
    (isExtremeRayOfCone_iff).1 hr_cone
  have hr_hull : r ∈ PointedCone.hull ℝ ({r} : Set (Fin n → ℝ)) :=
    PointedCone.subset_hull (by simp)
  exact hedge.isExtreme.subset hr_hull

/-- Helper for Exercise 3.37: a barycentric combination of the listed vertices belongs to `P`. -/
lemma listedVertexCombination_mem_polyhedron
    {n p : ℕ}
    {P : Set (Fin n → ℝ)}
    {V : Matrix (Fin n) (Fin p) ℝ}
    (hpolyhedron : is_polyhedron P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    {lam : Fin p → ℝ}
    (hlam_nonneg : ∀ i : Fin p, 0 ≤ lam i)
    (hlam_sum : ∑ i, lam i = 1) :
    ∑ i, lam i • Vᵀ i ∈ P := by
  -- First place the explicit coefficient sum in the convex hull of the listed vertices.
  have hconv_mem : ∑ i, lam i • Vᵀ i ∈ convexHull ℝ (Set.range Vᵀ) := by
    exact mem_convexHull_range_iff_exists_barycentric_weights.mpr ⟨lam, hlam_nonneg, hlam_sum, rfl⟩
  have hvertices_subset : Set.range Vᵀ ⊆ P := by
    intro x hx
    rcases hx with ⟨i, rfl⟩
    have hvertex_mem : Vᵀ i ∈ P.extremePoints ℝ := by
      rw [← hvertices]
      exact Set.mem_range_self i
    exact extremePoints_subset hvertex_mem
  -- Then use convexity of the ambient polyhedron.
  exact convexHull_min hvertices_subset (convex_of_is_polyhedron hpolyhedron) hconv_mem

/-- Helper for Exercise 3.37: a nonnegative combination of the listed extreme rays is a recession
direction of `P`. -/
lemma nonnegativeListedRayCombination_mem_recessionCone
    {n q : ℕ}
    {P : Set (Fin n → ℝ)}
    {R : Matrix (Fin n) (Fin q) ℝ}
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    {mu : Fin q → ℝ}
    (hmu_nonneg : ∀ j : Fin q, 0 ≤ mu j) :
    ∑ j, mu j • Rᵀ j ∈ recessionCone P := by
  -- Package the coefficients as a conic combination in the pointed cone of recession directions.
  change ∑ j, mu j • Rᵀ j ∈ (recessionPointedCone ℝ P : Set (Fin n → ℝ))
  exact PointedCone.conicCombination_mem
    (r := fun j : Fin q ↦ Rᵀ j)
    (x := ∑ j, mu j • Rᵀ j)
    (fun j ↦ isExtremeRayOfPointedPolyhedron_mem_recessionCone (hrays j))
    ⟨mu, hmu_nonneg, rfl⟩

/-- Helper for Exercise 3.37: lifted feasibility rewrites directly to the visible
`x = V λ + R μ` representation. -/
lemma vertexRayLiftedFeasible_eq_repr
    {n p q : ℕ}
    {V : Matrix (Fin n) (Fin p) ℝ}
    {R : Matrix (Fin n) (Fin q) ℝ}
    {y : (Fin n → ℝ) × (Fin p → ℝ) × (Fin q → ℝ)}
    (hy : VertexRayLiftedFeasible V R y) :
    y.1 = V *ᵥ y.2.1 + R *ᵥ y.2.2 := by
  -- Compare coordinates and solve the affine equation produced by `eq_zero`.
  ext i
  have hi : y.1 i - (V *ᵥ y.2.1) i - (R *ᵥ y.2.2) i = 0 := by
    simpa using congrArg (fun z ↦ z i) hy.eq_zero
  have hi' : y.1 i = (V *ᵥ y.2.1) i + (R *ᵥ y.2.2) i := by
    linarith
  simpa using hi'

/-- Helper for Exercise 3.37: any feasible triple `(x, λ, μ)` in the lifted system projects to a
point of `P`. -/
lemma mem_polyhedron_of_vertexRayLiftedFeasible
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    {V : Matrix (Fin n) (Fin p) ℝ}
    {R : Matrix (Fin n) (Fin q) ℝ}
    (hpolyhedron : is_polyhedron P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    {y : (Fin n → ℝ) × (Fin p → ℝ) × (Fin q → ℝ)}
    (hy : VertexRayLiftedFeasible V R y) :
    y.1 ∈ P := by
  -- Rewrite the lifted feasibility equations into the visible vertex-plus-ray decomposition.
  have hvertex_mem : V *ᵥ y.2.1 ∈ P := by
    rw [matrix_mulVec_eq_sum_transposeColumns]
    exact listedVertexCombination_mem_polyhedron hpolyhedron hvertices hy.lambda_nonneg
      hy.lambda_sum_one
  have hray_mem : R *ᵥ y.2.2 ∈ recessionCone P := by
    rw [matrix_mulVec_eq_sum_transposeColumns]
    exact nonnegativeListedRayCombination_mem_recessionCone
      (P := P) (R := R) hrays hy.mu_nonneg
  -- Route correction: use the stable representation lemma instead of repeating the coordinate
  -- `linarith` argument at each consumer.
  have hy_repr : y.1 = V *ᵥ y.2.1 + R *ᵥ y.2.2 := vertexRayLiftedFeasible_eq_repr hy
  -- A recession direction may be added to any point of `P`, in particular with scale `1`.
  have hsum_mem : V *ᵥ y.2.1 + (1 : ℝ) • (R *ᵥ y.2.2) ∈ P :=
    (mem_recessionCone_iff.mp hray_mem) hvertex_mem 1 zero_le_one
  simpa [hy_repr] using hsum_mem

/-- Helper for Exercise 3.37: once a point of `P` is split into a convex-hull vertex part and a
cone part generated by extreme rays, the local coefficient APIs convert that split into the exact
listed `λ, μ` representation on the columns of `V` and `R`. -/
lemma existsListedVertexRayWeightDecompositionOfSplit
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hP_nonempty : P.Nonempty)
    (hpolyhedron : is_polyhedron P)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {x : Fin n → ℝ}
    (hsplit :
      ∃ vertexPart rayPart : Fin n → ℝ,
        vertexPart ∈ convexHull ℝ (P.extremePoints ℝ) ∧
        rayPart ∈ PointedCone.hull ℝ {r | IsExtremeRayOfPolyhedron P r} ∧
        x = vertexPart + rayPart) :
    ∃ lam : Fin p → ℝ, ∃ mu : Fin q → ℝ,
      (∀ i : Fin p, 0 ≤ lam i) ∧
      (∀ j : Fin q, 0 ≤ mu j) ∧
      (∑ i, lam i = 1) ∧
      x = ∑ i, lam i • Vᵀ i + ∑ j, mu j • Rᵀ j := by
  rcases hsplit with ⟨vertexPart, rayPart, hvertexPart, hrayPart, rfl⟩
  -- Rewrite the vertex part through the listed vertex family and extract barycentric weights.
  have hvertexPart_listed : vertexPart ∈ convexHull ℝ (Set.range Vᵀ) := by
    rw [hvertices]
    exact hvertexPart
  rcases
      mem_convexHull_range_iff_exists_barycentric_weights.mp hvertexPart_listed with
    ⟨lam, hlam_nonneg, hlam_sum, hvertex_repr⟩
  -- Rewrite the ray part as a finite conic combination of extreme rays, then transport that
  -- combination to the listed representative family `Rᵀ`.
  have hrayPart_cone : rayPart ∈ cone {r | IsExtremeRayOfPolyhedron P r} := by
    simpa [pointedConeHull_eq_cone] using hrayPart
  rcases (mem_cone_iff.mp hrayPart_cone) with ⟨q', r, hr_source, hray_comb⟩
  rcases isConicCombination_iff.mp hray_comb with ⟨coeff, hcoeff_nonneg, hray_repr⟩
  have hr_extreme : ∀ j : Fin q', IsExtremeRayOfPolyhedron P (r j) := by
    intro j
    exact hr_source j
  have hrayPart_listed : rayPart ∈ finitely_generated_cone Rᵀ := by
    simpa [hray_repr] using
      (nonnegativeExtremeRayCombination_mem_listedCone
        R r hP_nonempty hpolyhedron hpointed hrays h_extreme_rep hr_extreme coeff
        hcoeff_nonneg)
  rcases (mem_finitely_generated_cone_iff.mp hrayPart_listed) with ⟨mu, hmu_nonneg, hmu_repr⟩
  refine ⟨lam, mu, hlam_nonneg, hmu_nonneg, hlam_sum, ?_⟩
  -- Assemble the listed vertex and ray representations back into the original point.
  calc
    vertexPart + rayPart = (∑ i, lam i • Vᵀ i) + rayPart := by rw [hvertex_repr]
    _ = (∑ i, lam i • Vᵀ i) + ∑ j, mu j • Rᵀ j := by rw [hmu_repr]

/-- Helper for Exercise 3.37: every point of `P` should admit the exact `(λ, μ)` witness needed by
`vertex_ray_polyhedron_eq_x_projection`. -/
lemma existsVertexRayLiftedFeasibleOfMemPolyhedron
    {n p q : ℕ}
    (P : Set (Fin n → ℝ))
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {x : Fin n → ℝ}
    (hx : x ∈ P) :
    ∃ lam : Fin p → ℝ, ∃ mu : Fin q → ℝ, VertexRayLiftedFeasible V R (x, lam, mu) := by
  have hsplit :
      ∃ vertexPart rayPart : Fin n → ℝ,
        vertexPart ∈ convexHull ℝ (P.extremePoints ℝ) ∧
        rayPart ∈ PointedCone.hull ℝ {r | IsExtremeRayOfPolyhedron P r} ∧
        x = vertexPart + rayPart := by
    -- Corollary 3.42 already gives the coarse vertex-plus-extreme-ray split for pointed
    -- polyhedra.
    exact exists_vertex_part_add_extreme_ray_part_of_mem_polyhedron hpolyhedron hpointed hx
  rcases existsListedVertexRayWeightDecompositionOfSplit
      V R ⟨x, hx⟩ hpolyhedron hpointed hvertices hrays h_extreme_rep hsplit with
    ⟨lam, mu, hlam_nonneg, hmu_nonneg, hlam_sum, hx_repr⟩
  have hx_repr' : x = V *ᵥ lam + R *ᵥ mu := by
    simpa [matrix_mulVec_eq_sum_transposeColumns] using hx_repr
  refine ⟨lam, mu, ?_⟩
  refine
    { eq_zero := ?_
      lambda_nonneg := hlam_nonneg
      mu_nonneg := hmu_nonneg
      lambda_sum_one := hlam_sum }
  -- Convert the explicit listed sum back to the lifted feasibility equation.
  ext i
  have hi := congrArg (fun z ↦ z i) hx_repr'
  have hi' : x i = (V *ᵥ lam) i + (R *ᵥ mu) i := by
    simpa using hi
  have hgoal : x i - (V *ᵥ lam) i - (R *ᵥ mu) i = 0 := by
    linarith
  simpa using hgoal

/-- Helper for Exercise 3.37: a full-dimensional subset of `ℝ^n` is nonempty. -/
lemma nonempty_of_affineSpan_eq_top
    {n : ℕ} {P : Set (Fin n → ℝ)}
    (hfull : affineSpan ℝ P = ⊤) :
    P.Nonempty := by
  by_contra hP
  rw [Set.not_nonempty_iff_eq_empty] at hP
  simp [hP] at hfull

/-- Helper for Exercise 3.37: if a linear inequality is bounded above by `β` at a point `x` and at
every recession translate `x + a • r`, then the ray contribution `α · r` is nonpositive. -/
lemma dotProduct_nonpos_of_bound_at_point_and_translate
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {α r : Fin n → ℝ}
    {β : ℝ}
    (hP_nonempty : P.Nonempty)
    (hvalid : is_valid_inequality P α β)
    (hr : r ∈ recessionCone P) :
    α ⬝ᵥ r ≤ 0 := by
  obtain ⟨x0, hx0P⟩ := hP_nonempty
  rw [mem_recessionCone_iff] at hr
  -- If the recession slope were positive, a long enough recession step would violate validity.
  by_contra hnot
  have hslope_pos : 0 < α ⬝ᵥ r := lt_of_not_ge hnot
  let a : ℝ := (β - α ⬝ᵥ x0 + 1) / (α ⬝ᵥ r)
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    have hx0_valid : α ⬝ᵥ x0 ≤ β := hvalid hx0P
    refine div_nonneg ?_ hslope_pos.le
    linarith
  have hxa : x0 + a • r ∈ P := hr hx0P a ha_nonneg
  have hvalid_a : α ⬝ᵥ (x0 + a • r) ≤ β := hvalid hxa
  have hdot : α ⬝ᵥ (x0 + a • r) = α ⬝ᵥ x0 + a * (α ⬝ᵥ r) := by
    simp [dotProduct_add, dotProduct_smul]
  have ha_mul : a * (α ⬝ᵥ r) = β - α ⬝ᵥ x0 + 1 := by
    dsimp [a]
    field_simp [hslope_pos.ne']
  rw [hdot, ha_mul] at hvalid_a
  linarith

/-- Helper for Exercise 3.37: every valid inequality of the polyhedron represented by the listed
vertices `Vᵀ` and extreme rays `Rᵀ` lies in the source-facing dual cone
`vertex_ray_dual_cone V R`. -/
lemma mem_vertexRayDualCone_of_validInequality
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    {V : Matrix (Fin n) (Fin p) ℝ}
    {R : Matrix (Fin n) (Fin q) ℝ}
    (hfull : affineSpan ℝ P = ⊤)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    (hvalid : is_valid_inequality P α β) :
    (α, β) ∈ vertex_ray_dual_cone V R := by
  have hP_nonempty : P.Nonempty := nonempty_of_affineSpan_eq_top hfull
  refine ⟨?_, ?_⟩
  · intro i
    -- Each listed vertex lies in `P`, so validity gives the vertex-side inequality directly.
    have hvertex_mem : Vᵀ i ∈ P := by
      have hvertex_extreme : Vᵀ i ∈ P.extremePoints ℝ := by
        rw [← hvertices]
        exact Set.mem_range_self i
      exact extremePoints_subset hvertex_extreme
    have hle : α ⬝ᵥ Vᵀ i ≤ β := hvalid hvertex_mem
    simpa [Matrix.vecMul, dotProduct] using hle
  · intro j
    -- Each listed extreme ray is a recession direction, so a positive slope would violate
    -- validity along a long enough recession translate.
    have hray_mem_recession : Rᵀ j ∈ recessionCone P := by
      -- Route correction: reuse the established recession-direction bridge instead of rebuilding
      -- the singleton-ray-hull witness by hand.
      exact isExtremeRayOfPointedPolyhedron_mem_recessionCone (hrays j)
    have hray_nonpos : α ⬝ᵥ Rᵀ j ≤ 0 := by
      exact dotProduct_nonpos_of_bound_at_point_and_translate hP_nonempty hvalid hray_mem_recession
    simpa [Matrix.vecMul, dotProduct] using hray_nonpos

/-- Helper for Exercise 3.37: every pair in `vertex_ray_dual_cone V R` defines a valid inequality
for the represented polyhedron `P`. -/
lemma validInequality_of_mem_vertexRayDualCone
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    {V : Matrix (Fin n) (Fin p) ℝ}
    {R : Matrix (Fin n) (Fin q) ℝ}
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    (hdual : (α, β) ∈ vertex_ray_dual_cone V R) :
    is_valid_inequality P α β := by
  intro x hx
  rcases existsVertexRayLiftedFeasibleOfMemPolyhedron
      P V R hpolyhedron hpointed hvertices hrays h_extreme_rep hx with
    ⟨lam, mu, hfeas⟩
  have hx_repr : x = V *ᵥ lam + R *ᵥ mu := by
    ext i
    have hi : x i - (V *ᵥ lam) i - (R *ᵥ mu) i = 0 := by
      simpa using congrArg (fun z ↦ z i) hfeas.eq_zero
    have hi' : x i = (V *ᵥ lam) i + (R *ᵥ mu) i := by
      linarith
    simpa [Pi.add_apply] using hi'
  have hvertex_part : α ⬝ᵥ (V *ᵥ lam) ≤ β := by
    calc
      α ⬝ᵥ (V *ᵥ lam) = (α ᵥ* V) ⬝ᵥ lam := by
        rw [Matrix.dotProduct_mulVec]
      _ = ∑ i, (α ᵥ* V) i * lam i := by
        simp [dotProduct]
      _ ≤ ∑ i, β * lam i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left (hdual.1 i) (hfeas.lambda_nonneg i)
      _ = β * ∑ i, lam i := by
        rw [Finset.mul_sum]
      _ = β := by
        rw [hfeas.lambda_sum_one, mul_one]
  have hray_part : α ⬝ᵥ (R *ᵥ mu) ≤ 0 := by
    calc
      α ⬝ᵥ (R *ᵥ mu) = (α ᵥ* R) ⬝ᵥ mu := by
        rw [Matrix.dotProduct_mulVec]
      _ = ∑ j, (α ᵥ* R) j * mu j := by
        simp [dotProduct]
      _ ≤ ∑ j, 0 * mu j := by
        refine Finset.sum_le_sum ?_
        intro j hj
        exact mul_le_mul_of_nonneg_right (hdual.2 j) (hfeas.mu_nonneg j)
      _ = 0 := by simp
  calc
    α ⬝ᵥ x = α ⬝ᵥ (V *ᵥ lam + R *ᵥ mu) := by rw [hx_repr]
    _ = α ⬝ᵥ (V *ᵥ lam) + α ⬝ᵥ (R *ᵥ mu) := by simp [dotProduct_add]
    _ ≤ β + 0 := add_le_add hvertex_part hray_part
    _ = β := by ring

/-- Helper for Exercise 3.37: if `P` is represented by the columns of `V` as vertices and the
columns of `R` form a representative family of all extreme rays of `P` up to `SameRay ℝ`, then
`P` is exactly the `x`-projection of the lifted system with variables `(x, λ, μ)` satisfying
`x - V λ - R μ = 0`, `λ ≥ 0`, `μ ≥ 0`, and `1ᵀ λ = 1`. -/
theorem vertex_ray_polyhedron_eq_x_projection
    {n p q : ℕ}
    (P : Set (Fin n → ℝ))
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j)) :
    P =
      Prod.fst ''
        {y : (Fin n → ℝ) × (Fin p → ℝ) × (Fin q → ℝ) | VertexRayLiftedFeasible V R y} :=
  by
    ext x
    constructor
    · intro hx
      -- Route correction: call the exact witness API needed by the projection statement.
      rcases existsVertexRayLiftedFeasibleOfMemPolyhedron
          P V R hpolyhedron hpointed hvertices hrays h_extreme_rep hx with
        ⟨lam, mu, hfeas⟩
      exact ⟨(x, lam, mu), hfeas, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      -- The reverse inclusion is elementary: barycentric vertex combinations stay in `P`, and
      -- nonnegative ray combinations are recession directions of `P`.
      exact mem_polyhedron_of_vertexRayLiftedFeasible hpolyhedron hvertices hrays hy

/-- Helper for Exercise 3.37: under the exercise hypotheses, the source-facing cone
`vertex_ray_dual_cone V R` is pointed. -/
theorem vertex_ray_dual_cone_pointed
    {n p q : ℕ}
    (P : Set (Fin n → ℝ))
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j)) :
    is_pointed (vertex_ray_dual_cone V R) :=
  by
    rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
    intro u hu
    rcases u with ⟨α, β⟩
    have hzero_mem : ((0 : Fin n → ℝ), (0 : ℝ)) ∈ vertex_ray_dual_cone V R := by
      constructor <;> intro i <;> simp
    rw [mem_linealitySpace_iff] at hu
    have hu_pos : (α, β) ∈ vertex_ray_dual_cone V R := by
      simpa using hu hzero_mem 1
    have hu_neg : (-α, -β) ∈ vertex_ray_dual_cone V R := by
      simpa using hu hzero_mem (-1)
    have hvalid_pos :
        is_valid_inequality P α β :=
      validInequality_of_mem_vertexRayDualCone
        hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hu_pos
    have hvalid_neg :
        is_valid_inequality P (-α) (-β) :=
      validInequality_of_mem_vertexRayDualCone
        hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hu_neg
    have hsubset : P ⊆ {x : Fin n → ℝ | α ⬝ᵥ x = β} := by
      intro x hx
      have hle : α ⬝ᵥ x ≤ β := hvalid_pos hx
      have hge : β ≤ α ⬝ᵥ x := by
        have hneg : -(α ⬝ᵥ x) ≤ -β := by
          simpa [dotProduct, Finset.mul_sum, neg_add_rev, sub_eq_add_neg, add_comm, add_left_comm,
            add_assoc] using hvalid_neg hx
        linarith
      exact le_antisymm hle hge
    have hspan_subset :
        (affineSpan ℝ P : Set (Fin n → ℝ)) ⊆ {x : Fin n → ℝ | α ⬝ᵥ x = β} :=
      affineSpan_subset_hyperplane_of_subset hsubset
    have hall : ∀ x : Fin n → ℝ, α ⬝ᵥ x = β := by
      intro x
      have hx_aff : x ∈ affineSpan ℝ P := by
        rw [hfull]
        simp
      exact hspan_subset hx_aff
    have hβ : β = 0 := by
      simpa using (hall 0).symm
    have hα : α = 0 := by
      ext i
      have hi := hall (Pi.single i 1)
      simpa [hβ, dotProduct, Pi.single_apply] using hi
    ext <;> simp [hα, hβ]

/-- Helper for Exercise 3.37: the vertex rows of the transposed lifted matrix evaluate
`Fin.snoc α (-β)` as the inequalities `α ᵥ* V ≤ β`. -/
lemma liftedVertexRayMatrixTranspose_mulVec_snocNeg_vertex
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (α : Fin n → ℝ)
    (β : ℝ)
    (i : Fin p) :
    ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
        (finSumFinEquiv (Sum.inl i)) =
      (α ᵥ* V) i - β := by
  -- Expand the `i`-th lifted vertex row and evaluate it on the homogenized signed pair.
  simp [vertexRayLiftedMatrix, Matrix.mulVec, dotProduct, Matrix.vecMul, Fin.sum_univ_castSucc,
    sub_eq_add_neg, add_comm, mul_comm]

/-- Helper for Exercise 3.37: the ray rows of the transposed lifted matrix evaluate
`Fin.snoc α (-β)` as the inequalities `α ᵥ* R ≤ 0`. -/
lemma liftedVertexRayMatrixTranspose_mulVec_snocNeg_ray
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (α : Fin n → ℝ)
    (β : ℝ)
    (j : Fin q) :
    ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
        (finSumFinEquiv (Sum.inr j)) =
      (α ᵥ* R) j := by
  -- Expand the `j`-th lifted ray row; its last coordinate is zero, so no `β` term appears.
  simp [vertexRayLiftedMatrix, Matrix.mulVec, dotProduct, Matrix.vecMul, Fin.sum_univ_castSucc,
    add_comm, mul_comm]

/-- Helper for Exercise 3.37: a lifted vertex row is active at `Fin.snoc α (-β)` exactly when the
corresponding listed vertex is tight for `α · x ≤ β`. -/
lemma lifted_vertex_row_active_iff
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (α : Fin n → ℝ)
    (β : ℝ)
    (i : Fin p) :
    ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
        (finSumFinEquiv (Sum.inl i)) = 0 ↔
      (α ᵥ* V) i = β := by
  -- Rewrite the lifted row evaluation to the source slack `(α V)_i - β`.
  rw [liftedVertexRayMatrixTranspose_mulVec_snocNeg_vertex]
  constructor <;> intro h <;> linarith

/-- Helper for Exercise 3.37: a lifted ray row is active at `Fin.snoc α (-β)` exactly when the
corresponding listed ray is tight for `α · r ≤ 0`. -/
lemma lifted_ray_row_active_iff
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (α : Fin n → ℝ)
    (β : ℝ)
    (j : Fin q) :
    ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
        (finSumFinEquiv (Sum.inr j)) = 0 ↔
      (α ᵥ* R) j = 0 := by
  -- Rewrite the lifted row evaluation to the source ray inequality value.
  rw [liftedVertexRayMatrixTranspose_mulVec_snocNeg_ray]

/-- Helper for Exercise 3.37: every lifted vertex row has last coordinate `1`. -/
lemma lifted_vertex_row_last_coordinate
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (i : Fin p) :
    ((vertexRayLiftedMatrix V R).transpose (finSumFinEquiv (Sum.inl i))) (Fin.last n) = 1 := by
  -- Unfold the lifted matrix only at the last coordinate of the chosen vertex row.
  simp [vertexRayLiftedMatrix, Fin.lastCases]

/-- Helper for Exercise 3.37: every lifted ray row has last coordinate `0`. -/
lemma lifted_ray_row_last_coordinate
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (j : Fin q) :
    ((vertexRayLiftedMatrix V R).transpose (finSumFinEquiv (Sum.inr j))) (Fin.last n) = 0 := by
  -- Unfold the lifted matrix only at the last coordinate of the chosen ray row.
  simp [vertexRayLiftedMatrix, Fin.lastCases]

/-- Helper for Exercise 3.37: the source-facing cone
`vertex_ray_dual_cone V R` is exactly the homogeneous system cut out by the transposed lifted
vertex-ray matrix evaluated at `Fin.snoc α (-β)`. -/
lemma signedPair_mem_liftedDualCone_iff
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (α : Fin n → ℝ)
    (β : ℝ) :
    (α, β) ∈ vertex_ray_dual_cone V R ↔
      Fin.snoc α (-β) ∈
        polyhedron_le_set (vertexRayLiftedMatrix V R).transpose 0 := by
  constructor
  · rintro ⟨hV, hR⟩
    -- Check the lifted homogeneous system one row family at a time.
    change (vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β) ≤ 0
    intro t
    cases hsplit : finSumFinEquiv.symm t with
    | inl i =>
        have ht : t = finSumFinEquiv (Sum.inl i) := by
          simpa using congrArg finSumFinEquiv hsplit
        rw [ht, liftedVertexRayMatrixTranspose_mulVec_snocNeg_vertex]
        exact sub_nonpos.mpr (hV i)
    | inr j =>
        have ht : t = finSumFinEquiv (Sum.inr j) := by
          simpa using congrArg finSumFinEquiv hsplit
        rw [ht, liftedVertexRayMatrixTranspose_mulVec_snocNeg_ray]
        exact hR j
  · intro hs
    -- Read the vertex and ray inequalities back from the corresponding lifted rows.
    change (vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β) ≤ 0 at hs
    refine ⟨?_, ?_⟩
    · intro i
      have hi := hs (finSumFinEquiv (Sum.inl i))
      rw [liftedVertexRayMatrixTranspose_mulVec_snocNeg_vertex] at hi
      exact sub_nonpos.mp hi
    · intro j
      have hj := hs (finSumFinEquiv (Sum.inr j))
      rw [liftedVertexRayMatrixTranspose_mulVec_snocNeg_ray] at hj
      exact hj

/-- Helper for Exercise 3.37: encode a signed pair `(α, β)` as the homogenized lifted vector
`Fin.snoc α (-β)`. -/
abbrev signedPairToLifted
    {n : ℕ} (u : (Fin n → ℝ) × ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc u.1 (-u.2)

/-- Helper for Exercise 3.37: decode a lifted vector back to the signed pair formed by its first
`n` coordinates and the negated last coordinate. -/
abbrev liftedToSignedPair
    {n : ℕ} (rbar : Fin (n + 1) → ℝ) : (Fin n → ℝ) × ℝ :=
  (fun i ↦ rbar i.castSucc, -rbar (Fin.last n))

/-- Helper for Exercise 3.37: decoding an encoded signed pair recovers the original pair. -/
lemma liftedToSignedPair_signedPairToLifted
    {n : ℕ} (u : (Fin n → ℝ) × ℝ) :
    liftedToSignedPair (signedPairToLifted u) = u := by
  -- Compare the first `n` coordinates and the negated last coordinate separately.
  rcases u with ⟨α, β⟩
  refine Prod.ext ?_ ?_
  · funext i
    simp [liftedToSignedPair, signedPairToLifted]
  · simp [liftedToSignedPair, signedPairToLifted]

/-- Helper for Exercise 3.37: encoding the decoded coordinates of a lifted vector recovers that
vector. -/
lemma signedPairToLifted_liftedToSignedPair
    {n : ℕ} (rbar : Fin (n + 1) → ℝ) :
    signedPairToLifted (liftedToSignedPair rbar) = rbar := by
  -- A function on `Fin (n + 1)` is determined by its first `n` coordinates and its last one.
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [liftedToSignedPair, signedPairToLifted]
  · intro i'
    simp [liftedToSignedPair, signedPairToLifted]

/-- Helper for Exercise 3.37: encoding commutes with addition on signed pairs. -/
lemma signedPairToLifted_add
    {n : ℕ} (u v : (Fin n → ℝ) × ℝ) :
    signedPairToLifted (u + v) = signedPairToLifted u + signedPairToLifted v := by
  -- Check the first `n` coordinates and the last coordinate of the lifted vector separately.
  rcases u with ⟨α, β⟩
  rcases v with ⟨γ, δ⟩
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simpa [signedPairToLifted] using neg_add β δ
  · intro i'
    simp [signedPairToLifted]

/-- Helper for Exercise 3.37: encoding commutes with scalar multiplication on signed pairs. -/
lemma signedPairToLifted_smul
    {n : ℕ} (a : ℝ) (u : (Fin n → ℝ) × ℝ) :
    signedPairToLifted (a • u) = a • signedPairToLifted u := by
  -- The sign on the last coordinate is compatible with scalar multiplication.
  ext i
  refine Fin.lastCases ?_ ?_ i
  · simp [signedPairToLifted]
  · intro i'
    simp [signedPairToLifted]

/-- Helper for Exercise 3.37: encoding signed pairs as lifted vectors is a linear map. -/
def signedPairToLiftedLinearMap
    {n : ℕ} : ((Fin n → ℝ) × ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  { toFun := signedPairToLifted
    map_add' := signedPairToLifted_add
    map_smul' := signedPairToLifted_smul }

/-- Helper for Exercise 3.37: decoding commutes with addition of lifted vectors. -/
lemma liftedToSignedPair_add
    {n : ℕ} (rbar sbar : Fin (n + 1) → ℝ) :
    liftedToSignedPair (rbar + sbar) = liftedToSignedPair rbar + liftedToSignedPair sbar := by
  refine Prod.ext ?_ ?_
  · funext i
    simp [liftedToSignedPair]
  · change -(rbar (Fin.last n) + sbar (Fin.last n)) = -rbar (Fin.last n) + -sbar (Fin.last n)
    ring

/-- Helper for Exercise 3.37: decoding commutes with scalar multiplication of lifted vectors. -/
lemma liftedToSignedPair_smul
    {n : ℕ} (a : ℝ) (rbar : Fin (n + 1) → ℝ) :
    liftedToSignedPair (a • rbar) = a • liftedToSignedPair rbar := by
  refine Prod.ext ?_ ?_
  · funext i
    simp [liftedToSignedPair]
  · simp [liftedToSignedPair]

/-- Helper for Exercise 3.37: membership in the lifted homogeneous cone can be read back as
membership in the source-facing signed-pair cone. -/
lemma lifted_mem_vertexRayDualCone_iff
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (rbar : Fin (n + 1) → ℝ) :
    rbar ∈ matrix_polyhedral_cone (vertexRayLiftedMatrix V R).transpose ↔
      liftedToSignedPair rbar ∈ vertex_ray_dual_cone V R := by
  -- Rewrite the lifted vector as the canonical encoding of its decoded signed pair.
  rw [← signedPairToLifted_liftedToSignedPair rbar]
  simpa [signedPairToLifted, liftedToSignedPair, mem_matrix_polyhedral_cone] using
    (signedPair_mem_liftedDualCone_iff V R (liftedToSignedPair rbar).1 (liftedToSignedPair rbar).2).symm

/-- Helper for Exercise 3.37: an extreme ray generator of `vertex_ray_dual_cone V R` is, in
particular, a member of that cone. -/
lemma mem_vertexRayDualCone_of_isExtremeRay
    {n p q : ℕ}
    {V : Matrix (Fin n) (Fin p) ℝ}
    {R : Matrix (Fin n) (Fin q) ℝ}
    {α : Fin n → ℝ}
    {β : ℝ}
    (hExtreme : IsExtremeRayOfCone (vertex_ray_dual_cone V R) (α, β)) :
    (α, β) ∈ vertex_ray_dual_cone V R := by
  -- Unpack the edge witness and use that the generator lies in its own singleton ray hull.
  exact (isExtremeRayOfCone_iff.mp hExtreme).isExtreme.subset (singleton_ray_hull_self_mem (α, β))

/-- Helper for Exercise 3.37: the lifted homogeneous cone cut out by
`(vertexRayLiftedMatrix V R).transpose` is pointed whenever the source-facing signed-pair cone is
pointed. -/
lemma lifted_dual_cone_pointed
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j)) :
    is_pointed (matrix_polyhedral_cone (vertexRayLiftedMatrix V R).transpose) := by
  rw [is_pointed_iff_eq_zero_of_mem_linealitySpace]
  intro rbar hrbar
  let u : (Fin n → ℝ) × ℝ := liftedToSignedPair rbar
  have hu_lineal : u ∈ linealitySpace (vertex_ray_dual_cone V R) := by
    rw [mem_linealitySpace_iff]
    intro x hx a
    have hx_lift :
        signedPairToLifted x ∈ matrix_polyhedral_cone (vertexRayLiftedMatrix V R).transpose := by
      rw [lifted_mem_vertexRayDualCone_iff V R, liftedToSignedPair_signedPairToLifted]
      exact hx
    have hsum_lift :
        signedPairToLifted x + a • rbar ∈
          matrix_polyhedral_cone (vertexRayLiftedMatrix V R).transpose :=
      (mem_linealitySpace_iff.mp hrbar) hx_lift a
    have hsum_source :
        liftedToSignedPair (signedPairToLifted x + a • rbar) ∈ vertex_ray_dual_cone V R :=
      (lifted_mem_vertexRayDualCone_iff V R _).mp hsum_lift
    -- Route correction: move the lineality argument through the concrete encode/decode maps
    -- instead of unfolding the lifted matrix system directly.
    simpa [u, liftedToSignedPair_add, liftedToSignedPair_smul,
      liftedToSignedPair_signedPairToLifted] using hsum_source
  have hu_zero : u = 0 := by
    exact
      (is_pointed_iff_eq_zero_of_mem_linealitySpace.mp
        (vertex_ray_dual_cone_pointed P V R hpolyhedron hfull hpointed hvertices hrays
          h_extreme_rep)) u hu_lineal
  have hrbar_eq : rbar = signedPairToLifted u := by
    simpa [u] using (signedPairToLifted_liftedToSignedPair rbar).symm
  rw [hu_zero] at hrbar_eq
  ext i
  have hi := congrArg (fun f ↦ f i) hrbar_eq
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simpa [signedPairToLifted] using hi
  · simpa [signedPairToLifted] using hi

/-- Helper for Exercise 3.37: once the lifted homogeneous system is known to be pointed, it can
be viewed as a pointed cone with the same carrier. -/
lemma matrix_polyhedral_cone_as_pointedCone
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hpointed : is_pointed (matrix_polyhedral_cone A)) :
    ∃ K : PointedCone ℝ (Fin n → ℝ), (K : Set (Fin n → ℝ)) = matrix_polyhedral_cone A := by
  -- Reuse the canonical recession-cone carrier for the homogeneous system `A *ᵥ x ≤ 0`.
  let Q : Set (Fin n → ℝ) := polyhedron_le_set A 0
  have hQ_nonempty : Q.Nonempty := by
    refine ⟨0, ?_⟩
    simp [Q, polyhedron_le_set]
  refine ⟨recessionPointedCone ℝ Q, ?_⟩
  -- For a homogeneous system, the recession cone is the system itself.
  simpa [Q, matrix_polyhedral_cone] using
    recessionCone_polyhedron_eq_matrix_polyhedral_cone A 0 hQ_nonempty

/-- Helper for Exercise 3.37: an extreme ray of the signed-pair cone yields the `n` active
linearly independent lifted rows of the lifted homogeneous system after passing to
`Fin.snoc α (-β)`. -/
lemma lifted_dual_cone_extreme_ray_exists_active_linearlyIndependent_rows
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    (hExtreme : IsExtremeRayOfCone (vertex_ray_dual_cone V R) (α, β)) :
    ∃ I : Fin n ↪ Fin (p + q),
      (∀ k : Fin n,
        ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β)) (I k) = 0) ∧
        LinearIndependent ℝ
          (fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k)) := by
  let A : Matrix (Fin (p + q)) (Fin (n + 1)) ℝ := (vertexRayLiftedMatrix V R).transpose
  have hrbar_mem : signedPairToLifted (α, β) ∈ matrix_polyhedral_cone A := by
    rw [lifted_mem_vertexRayDualCone_iff V R, liftedToSignedPair_signedPairToLifted]
    exact mem_vertexRayDualCone_of_isExtremeRay hExtreme
  have hrbar_ne : signedPairToLifted (α, β) ≠ 0 := by
    intro hrbar_zero
    have hpair_zero : (α, β) = 0 := by
      simpa [liftedToSignedPair_signedPairToLifted] using congrArg liftedToSignedPair hrbar_zero
    exact extremeRay_ne_zero hExtreme hpair_zero
  have hpointed_lifted : is_pointed (matrix_polyhedral_cone A) := by
    simpa [A] using
      lifted_dual_cone_pointed V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep
  have hlifted_not_proper :
      ¬ ProperConicCombinationOfDistinctConeRays (matrix_polyhedral_cone A)
        (signedPairToLifted (α, β)) := by
    have hsource_not_proper :
        ¬ ProperConicCombinationOfDistinctConeRays (vertex_ray_dual_cone V R) (α, β) :=
      (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
        (vertex_ray_dual_cone_as_pointedCone V R)
        (mem_vertexRayDualCone_of_isExtremeRay hExtreme)
        (extremeRay_ne_zero hExtreme)).mp hExtreme
    intro hproper
    rcases hproper with
      ⟨rbar₁, rbar₂, hrbar₁, hrbar₂, hrbar₁_ne, hrbar₂_ne, hnot_same, μ₁, μ₂, hμ₁, hμ₂,
        hdecomp⟩
    let u₁ : (Fin n → ℝ) × ℝ := liftedToSignedPair rbar₁
    let u₂ : (Fin n → ℝ) × ℝ := liftedToSignedPair rbar₂
    have hu₁ : u₁ ∈ vertex_ray_dual_cone V R := (lifted_mem_vertexRayDualCone_iff V R _).mp hrbar₁
    have hu₂ : u₂ ∈ vertex_ray_dual_cone V R := (lifted_mem_vertexRayDualCone_iff V R _).mp hrbar₂
    have hu₁_ne : u₁ ≠ 0 := by
      intro hu₁_zero
      apply hrbar₁_ne
      calc
        rbar₁ = signedPairToLifted u₁ := by simpa [u₁] using (signedPairToLifted_liftedToSignedPair rbar₁).symm
        _ = 0 := by
              rw [hu₁_zero]
              ext i
              rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
              · simp [signedPairToLifted]
              · simp [signedPairToLifted]
    have hu₂_ne : u₂ ≠ 0 := by
      intro hu₂_zero
      apply hrbar₂_ne
      calc
        rbar₂ = signedPairToLifted u₂ := by simpa [u₂] using (signedPairToLifted_liftedToSignedPair rbar₂).symm
        _ = 0 := by
              rw [hu₂_zero]
              ext i
              rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
              · simp [signedPairToLifted]
              · simp [signedPairToLifted]
    have hu_not_same : ¬ SameRay ℝ u₁ u₂ := by
      intro hu_same
      apply hnot_same
      have hmap :
          SameRay ℝ (signedPairToLifted u₁) (signedPairToLifted u₂) :=
        SameRay.map (signedPairToLiftedLinearMap (n := n)) hu_same
      simpa [u₁, u₂, signedPairToLifted_liftedToSignedPair] using hmap
    have hsource_decomp : (α, β) = μ₁ • u₁ + μ₂ • u₂ := by
      have := congrArg liftedToSignedPair hdecomp
      simpa [u₁, u₂, liftedToSignedPair_signedPairToLifted, liftedToSignedPair_add,
        liftedToSignedPair_smul] using this
    exact hsource_not_proper
      ⟨u₁, u₂, hu₁, hu₂, hu₁_ne, hu₂_ne, hu_not_same, μ₁, μ₂, hμ₁, hμ₂, hsource_decomp⟩
  have hlifted_extreme : IsExtremeRayOfCone (matrix_polyhedral_cone A) (signedPairToLifted (α, β)) :=
    (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
      (matrix_polyhedral_cone_as_pointedCone A hpointed_lifted) hrbar_mem hrbar_ne).mpr
      hlifted_not_proper
  have hP_nonempty : (polyhedron_le_set A 0).Nonempty := by
    refine ⟨0, ?_⟩
    simp [polyhedron_le_set]
  have hP_pointed : is_pointed (polyhedron_le_set A 0) := by
    simpa [matrix_polyhedral_cone] using hpointed_lifted
  have hpoly_extreme : IsExtremeRayOfPolyhedron (polyhedron_le_set A 0) (signedPairToLifted (α, β)) :=
    by
      rw [isExtremeRayOfPolyhedron_iff, recessionCone_polyhedron_eq_matrix_polyhedral_cone A 0
        hP_nonempty]
      exact hlifted_extreme
  simpa [A, signedPairToLifted] using
    extreme_recession_ray_exists_active_linearlyIndependent_rows A 0 hP_nonempty hP_pointed
      hpoly_extreme

/-- Helper for Exercise 3.37: a listed vertex that is tight for `(α, β)` lies in the equality
face `face_set P α β`. -/
lemma mem_faceSet_of_tightVertex
    {n p : ℕ}
    {P : Set (Fin n → ℝ)}
    {V : Matrix (Fin n) (Fin p) ℝ}
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    {α : Fin n → ℝ}
    {β : ℝ}
    {i : Fin p}
    (hi : (α ᵥ* V) i = β) :
    Vᵀ i ∈ face_set P α β := by
  -- Membership in the equality face is exactly ambient feasibility plus tightness of the row.
  have hvertex_mem : Vᵀ i ∈ P := by
    have hvertex_extreme : Vᵀ i ∈ P.extremePoints ℝ := by
      rw [← hvertices]
      exact Set.mem_range_self i
    exact extremePoints_subset hvertex_extreme
  refine (mem_face_set_iff).2 ⟨hvertex_mem, ?_⟩
  -- Rewrite the tight lifted-row identity back to the source dot-product spelling.
  simpa [Matrix.vecMul, dotProduct] using hi

/-- Helper for Exercise 3.37: if some listed vertex is tight for `(α, β)`, then the equality face
`face_set P α β` is nonempty. -/
lemma faceSet_nonempty_of_exists_tightVertex
    {n p : ℕ}
    {P : Set (Fin n → ℝ)}
    {V : Matrix (Fin n) (Fin p) ℝ}
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    {α : Fin n → ℝ}
    {β : ℝ}
    (htight : ∃ i : Fin p, (α ᵥ* V) i = β) :
    (face_set P α β).Nonempty := by
  rcases htight with ⟨i, hi⟩
  -- The tight listed vertex itself is the required face point.
  exact ⟨Vᵀ i, mem_faceSet_of_tightVertex hvertices hi⟩

/-- Helper for Exercise 3.37: a point on the equality face admits lifted coefficients whose
positive support is concentrated on tight listed vertices and tight listed rays. -/
lemma tight_support_of_faceSet_point
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    {x : Fin n → ℝ}
    (hx : x ∈ face_set P α β)
    (hdual : (α, β) ∈ vertex_ray_dual_cone V R) :
    ∃ lam : Fin p → ℝ, ∃ mu : Fin q → ℝ,
      VertexRayLiftedFeasible V R (x, lam, mu) ∧
        (∀ i : Fin p, 0 < lam i → (α ᵥ* V) i = β) ∧
        (∀ j : Fin q, 0 < mu j → (α ᵥ* R) j = 0) := by
  have hxP : x ∈ P := (mem_face_set_iff.mp hx).1
  have hx_tight : α ⬝ᵥ x = β := (mem_face_set_iff.mp hx).2
  rcases existsVertexRayLiftedFeasibleOfMemPolyhedron
      P V R hpolyhedron hpointed hvertices hrays h_extreme_rep hxP with
    ⟨lam, mu, hfeas⟩
  refine ⟨lam, mu, hfeas, ?_, ?_⟩
  · intro i hi_pos
    -- Normalize the lifted feasibility witness before analyzing the slack sums.
    have hx_repr : x = V *ᵥ lam + R *ᵥ mu := vertexRayLiftedFeasible_eq_repr hfeas
    have hvertex_le : α ⬝ᵥ (V *ᵥ lam) ≤ β := by
      calc
        α ⬝ᵥ (V *ᵥ lam) = (α ᵥ* V) ⬝ᵥ lam := by
          rw [Matrix.dotProduct_mulVec]
        _ = ∑ k, (α ᵥ* V) k * lam k := by
          simp [dotProduct]
        _ ≤ ∑ k, β * lam k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left (hdual.1 k) (hfeas.lambda_nonneg k)
        _ = β * ∑ k, lam k := by
          rw [Finset.mul_sum]
        _ = β := by
          rw [hfeas.lambda_sum_one, mul_one]
    have hray_le : α ⬝ᵥ (R *ᵥ mu) ≤ 0 := by
      calc
        α ⬝ᵥ (R *ᵥ mu) = (α ᵥ* R) ⬝ᵥ mu := by
          rw [Matrix.dotProduct_mulVec]
        _ = ∑ j, (α ᵥ* R) j * mu j := by
          simp [dotProduct]
        _ ≤ ∑ j, 0 * mu j := by
          refine Finset.sum_le_sum ?_
          intro j hj
          exact mul_le_mul_of_nonneg_right (hdual.2 j) (hfeas.mu_nonneg j)
        _ = 0 := by simp
    have hx_split :
        α ⬝ᵥ x = α ⬝ᵥ (V *ᵥ lam) + α ⬝ᵥ (R *ᵥ mu) := by
      rw [hx_repr]
      simp [dotProduct_add]
    -- The ray contribution is nonpositive, so tightness of `x` forces the vertex average to
    -- achieve the upper bound `β`.
    have hvertex_eq : α ⬝ᵥ (V *ᵥ lam) = β := by
      linarith
    have hslack_sum :
        ∑ k, lam k * (β - (α ᵥ* V) k) = 0 := by
      calc
        ∑ k, lam k * (β - (α ᵥ* V) k)
            = ∑ k, (lam k * β - lam k * ((α ᵥ* V) k)) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                ring
        _ = (∑ k, lam k * β) - ∑ k, lam k * ((α ᵥ* V) k) := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ k, lam k) * β - ∑ k, ((α ᵥ* V) k * lam k) := by
              congr 1
              · rw [Finset.sum_mul]
              · refine Finset.sum_congr rfl ?_
                intro k hk
                ring
        _ = β * ∑ k, lam k - ∑ k, ((α ᵥ* V) k * lam k) := by
              ring
        _ = β - α ⬝ᵥ (V *ᵥ lam) := by
              rw [hfeas.lambda_sum_one, mul_one, Matrix.dotProduct_mulVec]
              simp [dotProduct]
        _ = 0 := by rw [hvertex_eq, sub_self]
    have hterm_zero :
        ∀ k : Fin p, lam k * (β - (α ᵥ* V) k) = 0 := by
      have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin p)), 0 ≤ lam k * (β - (α ᵥ* V) k) := by
        intro k hk
        exact mul_nonneg (hfeas.lambda_nonneg k) (sub_nonneg.mpr (hdual.1 k))
      simpa using (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hslack_sum
    have hgap_zero : β - (α ᵥ* V) i = 0 := by
      rcases mul_eq_zero.mp (hterm_zero i) with hlam_zero | hgap_zero
      · exact False.elim ((ne_of_gt hi_pos) hlam_zero)
      · exact hgap_zero
    linarith
  · intro j hj_pos
    -- Reuse the same canonical representation for the ray-support argument.
    have hx_repr : x = V *ᵥ lam + R *ᵥ mu := vertexRayLiftedFeasible_eq_repr hfeas
    have hvertex_le : α ⬝ᵥ (V *ᵥ lam) ≤ β := by
      calc
        α ⬝ᵥ (V *ᵥ lam) = (α ᵥ* V) ⬝ᵥ lam := by
          rw [Matrix.dotProduct_mulVec]
        _ = ∑ k, (α ᵥ* V) k * lam k := by
          simp [dotProduct]
        _ ≤ ∑ k, β * lam k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          simpa [mul_comm] using
            mul_le_mul_of_nonneg_left (hdual.1 k) (hfeas.lambda_nonneg k)
        _ = β * ∑ k, lam k := by
          rw [Finset.mul_sum]
        _ = β := by
          rw [hfeas.lambda_sum_one, mul_one]
    have hray_le : α ⬝ᵥ (R *ᵥ mu) ≤ 0 := by
      calc
        α ⬝ᵥ (R *ᵥ mu) = (α ᵥ* R) ⬝ᵥ mu := by
          rw [Matrix.dotProduct_mulVec]
        _ = ∑ k, (α ᵥ* R) k * mu k := by
          simp [dotProduct]
        _ ≤ ∑ k, 0 * mu k := by
          refine Finset.sum_le_sum ?_
          intro k hk
          exact mul_le_mul_of_nonneg_right (hdual.2 k) (hfeas.mu_nonneg k)
        _ = 0 := by simp
    have hx_split :
        α ⬝ᵥ x = α ⬝ᵥ (V *ᵥ lam) + α ⬝ᵥ (R *ᵥ mu) := by
      rw [hx_repr]
      simp [dotProduct_add]
    -- Route correction: isolate the ray sum after proving the vertex average already saturates
    -- `β`; then positive ray coefficients force zero slope term-by-term.
    have hray_eq_zero : α ⬝ᵥ (R *ᵥ mu) = 0 := by
      linarith
    have hslack_sum :
        ∑ k, mu k * (-(α ᵥ* R) k) = 0 := by
      calc
        ∑ k, mu k * (-(α ᵥ* R) k)
            = ∑ k, -((α ᵥ* R) k * mu k) := by
                refine Finset.sum_congr rfl ?_
                intro k hk
                ring
        _ = -∑ k, ((α ᵥ* R) k * mu k) := by
              rw [Finset.sum_neg_distrib]
        _ = -(α ⬝ᵥ (R *ᵥ mu)) := by
              rw [Matrix.dotProduct_mulVec]
              simp [dotProduct]
        _ = 0 := by rw [hray_eq_zero, neg_zero]
    have hterm_zero :
        ∀ k : Fin q, mu k * (-(α ᵥ* R) k) = 0 := by
      have hnonneg : ∀ k ∈ (Finset.univ : Finset (Fin q)), 0 ≤ mu k * (-(α ᵥ* R) k) := by
        intro k hk
        exact mul_nonneg (hfeas.mu_nonneg k) (neg_nonneg.mpr (hdual.2 k))
      simpa using (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hslack_sum
    have hgap_zero : -(α ᵥ* R) j = 0 := by
      rcases mul_eq_zero.mp (hterm_zero j) with hmu_zero | hgap_zero
      · exact False.elim ((ne_of_gt hj_pos) hmu_zero)
      · exact hgap_zero
    linarith

/-- Helper for Exercise 3.37: every nonempty equality face of a dual-cone inequality contains a
tight listed vertex. -/
lemma exists_tightVertex_of_faceSet_point
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    {x : Fin n → ℝ}
    (hx : x ∈ face_set P α β)
    (hdual : (α, β) ∈ vertex_ray_dual_cone V R) :
    ∃ i : Fin p, (α ᵥ* V) i = β := by
  rcases tight_support_of_faceSet_point
      V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hx hdual with
    ⟨lam, mu, hfeas, hlam_tight, _⟩
  by_contra htight
  -- If no listed vertex were tight, every barycentric weight would have to vanish, contradicting
  -- `∑ λ = 1`.
  have hnot_pos : ∀ i : Fin p, ¬ 0 < lam i := by
    intro i hi
    exact htight ⟨i, hlam_tight i hi⟩
  have hlam_zero : ∀ i : Fin p, lam i = 0 := by
    intro i
    exact le_antisymm (le_of_not_gt (hnot_pos i)) (hfeas.lambda_nonneg i)
  have : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = ∑ i, lam i := by symm; exact hfeas.lambda_sum_one
      _ = 0 := by simp [hlam_zero]
  exact one_ne_zero this

/-- Helper for Exercise 3.37: tightness of a summed valid inequality forces tightness of each
valid summand. -/
lemma sum_tight_implies_component_tight
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {α₁ α₂ x : Fin n → ℝ}
    {β₁ β₂ : ℝ}
    (hvalid₁ : is_valid_inequality P α₁ β₁)
    (hvalid₂ : is_valid_inequality P α₂ β₂)
    (hx : x ∈ face_set P (α₁ + α₂) (β₁ + β₂)) :
    x ∈ face_set P α₁ β₁ ∧ x ∈ face_set P α₂ β₂ := by
  have hxP : x ∈ P := (mem_face_set_iff.mp hx).1
  have hx_sum : (α₁ + α₂) ⬝ᵥ x = β₁ + β₂ := (mem_face_set_iff.mp hx).2
  have hle₁ : α₁ ⬝ᵥ x ≤ β₁ := hvalid₁ hxP
  have hle₂ : α₂ ⬝ᵥ x ≤ β₂ := hvalid₂ hxP
  have hx_sum' : α₁ ⬝ᵥ x + α₂ ⬝ᵥ x = β₁ + β₂ := by
    simpa [dotProduct_add] using hx_sum
  have heq₁ : α₁ ⬝ᵥ x = β₁ := by
    linarith
  have heq₂ : α₂ ⬝ᵥ x = β₂ := by
    linarith
  exact ⟨(mem_face_set_iff).2 ⟨hxP, heq₁⟩, (mem_face_set_iff).2 ⟨hxP, heq₂⟩⟩

/-- Helper for Exercise 3.37: the direction of an equality face lies in the kernel of the
exposing dot-product functional. -/
lemma face_set_direction_le_dotProduct_ker
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {α x₀ : Fin n → ℝ}
    {β : ℝ}
    (hx₀ : x₀ ∈ face_set P α β) :
    (affineSpan ℝ (face_set P α β)).direction ≤
      LinearMap.ker (dotProductStrongDual α).toLinearMap := by
  have hsubset : face_set P α β ⊆ {x : Fin n → ℝ | α ⬝ᵥ x = β} := by
    intro x hx
    exact (mem_face_set_iff.mp hx).2
  have hspan_subset :
      (affineSpan ℝ (face_set P α β) : Set (Fin n → ℝ)) ⊆
        {x : Fin n → ℝ | α ⬝ᵥ x = β} :=
    affineSpan_subset_hyperplane_of_subset hsubset
  have hx₀_aff : x₀ ∈ affineSpan ℝ (face_set P α β) := subset_affineSpan ℝ _ hx₀
  intro v hv
  rw [LinearMap.mem_ker]
  rw [AffineSubspace.mem_direction_iff_eq_vsub_right hx₀_aff] at hv
  rcases hv with ⟨x, hx_aff, rfl⟩
  -- Subtracting two points on the same supporting hyperplane kills the dot-product functional.
  have hx_eq : α ⬝ᵥ x = β := hspan_subset hx_aff
  have hx₀_eq : α ⬝ᵥ x₀ = β := (mem_face_set_iff.mp hx₀).2
  simp [dotProductStrongDual_apply, vsub_eq_sub, hx_eq, hx₀_eq]

/-- Helper for Exercise 3.37: on a full-dimensional polyhedron, a valid inequality whose equality
face is all of `P` must have zero coefficient pair. -/
lemma pair_eq_zero_of_faceSet_eq_univ_of_affineSpan_eq_top
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hfull : affineSpan ℝ P = ⊤)
    (hface_all : face_set P c δ = P) :
    (c, δ) = 0 := by
  have hsubset : P ⊆ {x : Fin n → ℝ | c ⬝ᵥ x = δ} := by
    intro x hx
    have hx_face : x ∈ face_set P c δ := by
      simpa [hface_all] using hx
    exact (mem_face_set_iff.mp hx_face).2
  have hspan_subset :
      (affineSpan ℝ P : Set (Fin n → ℝ)) ⊆ {x : Fin n → ℝ | c ⬝ᵥ x = δ} :=
    affineSpan_subset_hyperplane_of_subset hsubset
  have hall : ∀ x : Fin n → ℝ, c ⬝ᵥ x = δ := by
    intro x
    have hx_aff : x ∈ affineSpan ℝ P := by
      rw [hfull]
      simp
    exact hspan_subset hx_aff
  have hδ : δ = 0 := by
    simpa using (hall 0).symm
  have hc : c = 0 := by
    ext i
    have hi := hall (Pi.single i 1)
    simpa [hδ, dotProduct, Pi.single_apply] using hi
  ext <;> simp [hc, hδ]

/-- Helper for Exercise 3.37: the strong dual functional induced by a nonzero vector is nonzero. -/
lemma dotProductStrongDual_ne_zero_of_ne_zero
    {n : ℕ}
    {c : Fin n → ℝ}
    (hc : c ≠ 0) :
    dotProductStrongDual c ≠ 0 := by
  intro hzero
  apply hc
  ext i
  have hi := DFunLike.congr_fun hzero (Pi.single i 1)
  simpa [dotProductStrongDual_apply, dotProduct, Pi.single_apply] using hi

/-- Helper for Exercise 3.37: a nonzero dot-product functional on `ℝ^n` has kernel of codimension
one. -/
lemma finrank_ker_dotProductStrongDual_add_one_eq
    {n : ℕ}
    {c : Fin n → ℝ}
    (hc : c ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 = n := by
  have hexists : ∃ i, c i ≠ 0 := by
    by_contra h
    apply hc
    ext i
    exact not_not.mp ((not_exists.mp h) i)
  rcases hexists with ⟨i, hi⟩
  have hsurj : Function.Surjective (dotProductStrongDual c).toLinearMap := by
    intro y
    refine ⟨((c i)⁻¹ * y) • Pi.single i 1, ?_⟩
    calc
      dotProductStrongDual c (((c i)⁻¹ * y) • Pi.single i 1) = c i * ((c i)⁻¹ * y) := by
        rw [dotProductStrongDual_apply, dotProduct]
        simp [Pi.single_apply, hi]
      _ = y := by
        field_simp [hi]
  have hrange : LinearMap.range (dotProductStrongDual c).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hrange_finrank :
      Module.finrank ℝ (LinearMap.range (dotProductStrongDual c).toLinearMap) = 1 := by
    rw [hrange, finrank_top]
    simpa using (finrank_self ℝ)
  have hranknull :=
    LinearMap.finrank_range_add_finrank_ker (dotProductStrongDual c).toLinearMap
  rw [hrange_finrank] at hranknull
  simpa [Module.finrank_fintype_fun_eq_card, add_comm] using hranknull

/-- Helper for Exercise 3.37: a nonempty finite index type `Fin n` satisfies `(n - 1) + 1 = n`.
-/
lemma fin_sub_one_add_one_eq
    {n : ℕ}
    (k : Fin n) :
    (n - 1) + 1 = n := by
  have hn_pos : 0 < n := Fin.pos_iff_nonempty.mpr ⟨k⟩
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)

/-- Helper for Exercise 3.37: a nonzero vector in `ℝ^n` forces `n` to be positive. -/
lemma fin_dim_pos_of_ne_zero_vector
    {n : ℕ}
    {v : Fin n → ℝ}
    (hv : v ≠ 0) :
    0 < n := by
  by_cases hzero : n = 0
  · subst hzero
    exfalso
    apply hv
    ext i
    exact Fin.elim0 i
  · exact Nat.pos_of_ne_zero hzero

/-- Helper for Exercise 3.37: a nonzero valid inequality with a nonempty equality face cuts out a
proper face on any full-dimensional polyhedron. -/
lemma proper_face_of_valid_inequality_of_nonzero_of_nonempty_of_affineSpan_eq_top
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hvalid : is_valid_inequality P c δ)
    (hfull : affineSpan ℝ P = ⊤)
    (hpair_ne : (c, δ) ≠ 0)
    (hface_nonempty : (face_set P c δ).Nonempty) :
    is_proper_face P (face_set P c δ) := by
  have hface_ne : face_set P c δ ≠ P := by
    intro hface_all
    exact hpair_ne (pair_eq_zero_of_faceSet_eq_univ_of_affineSpan_eq_top hfull hface_all)
  have hface_ssubset : face_set P c δ ⊂ P := by
    refine ⟨?_, ?_⟩
    intro x hx
    exact (mem_face_set_iff.mp hx).1
    intro hP_subset
    exact hface_ne (Set.Subset.antisymm (fun x hx ↦ (mem_face_set_iff.mp hx).1) hP_subset)
  -- A nontrivial equality face of a valid inequality is a proper face by definition.
  exact
    (is_proper_face_iff).2
      ⟨isExposed_face_set_of_valid_inequality hvalid, hface_nonempty, hface_ssubset⟩

/-- Helper for Exercise 3.37: an outside point of the common facet has strictly positive deficits
for both valid inequalities. -/
lemma outside_point_gap_pos_of_same_facet
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c d : Fin n → ℝ}
    {δ ε : ℝ}
    (hvalid_c : is_valid_inequality P c δ)
    (hvalid_d : is_valid_inequality P d ε)
    (hface : face_set P c δ = face_set P d ε)
    {x0 : Fin n → ℝ}
    (hx0P : x0 ∈ P)
    (hx0_not_face : x0 ∉ face_set P c δ) :
    let gc : ℝ := δ - c ⬝ᵥ x0
    let gd : ℝ := ε - d ⬝ᵥ x0
    0 < gc ∧ 0 < gd := by
  dsimp
  have hx0_not_face_d : x0 ∉ face_set P d ε := by
    intro hx0_face_d
    exact hx0_not_face (by simpa [hface] using hx0_face_d)
  have hcx_lt : c ⬝ᵥ x0 < δ := by
    have hcx_ne : c ⬝ᵥ x0 ≠ δ := by
      intro hcx_eq
      exact hx0_not_face ((mem_face_set_iff).2 ⟨hx0P, hcx_eq⟩)
    exact lt_of_le_of_ne (hvalid_c hx0P) hcx_ne
  have hdx_lt : d ⬝ᵥ x0 < ε := by
    have hdx_ne : d ⬝ᵥ x0 ≠ ε := by
      intro hdx_eq
      exact hx0_not_face_d ((mem_face_set_iff).2 ⟨hx0P, hdx_eq⟩)
    exact lt_of_le_of_ne (hvalid_d hx0P) hdx_ne
  set gc : ℝ := δ - c ⬝ᵥ x0 with hgc_def
  set gd : ℝ := ε - d ⬝ᵥ x0 with hgd_def
  have hgc_pos : 0 < gc := by
    rw [hgc_def]
    exact sub_pos.mpr hcx_lt
  have hgd_pos : 0 < gd := by
    rw [hgd_def]
    exact sub_pos.mpr hdx_lt
  exact ⟨hgc_pos, hgd_pos⟩

/-- Helper for Exercise 3.37: the direction space of a facet equality face is exactly the kernel
of its exposing functional. -/
lemma common_facet_direction_eq_kernel_of_valid_inequality
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ : ℝ}
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hvalid : is_valid_inequality P c δ)
    (hfacet : is_facet P (face_set P c δ))
    (hcd_ne : (c, δ) ≠ 0) :
    (affineSpan ℝ (face_set P c δ)).direction =
      LinearMap.ker (dotProductStrongDual c).toLinearMap := by
  rcases hpolyhedron with ⟨m, A, b, rfl⟩
  obtain ⟨x₀, hx₀⟩ :=
    (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1
  have hP_nonempty : (polyhedron_le_set A b).Nonempty := by
    exact ⟨x₀, (mem_face_set_iff.mp hx₀).1⟩
  have hdir_le :
      (affineSpan ℝ (face_set (polyhedron_le_set A b) c δ)).direction ≤
        LinearMap.ker (dotProductStrongDual c).toLinearMap :=
    face_set_direction_le_dotProduct_ker hx₀
  have hc_ne : c ≠ 0 := by
    intro hc
    have hδ_zero : δ = 0 := by
      simpa [hc, dotProduct] using ((mem_face_set_iff.mp hx₀).2).symm
    exact hcd_ne (by ext <;> simp [hc, hδ_zero])
  have hface_codim :
      Module.finrank ℝ
          (affineSpan ℝ (face_set (polyhedron_le_set A b) c δ)).direction + 1 =
        Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction := by
    exact
      (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
        A b hP_nonempty (face_set (polyhedron_le_set A b) c δ)
        (isExposed_face_set_of_valid_inequality hvalid)).mp hfacet |>.2
  have hface_finrank :
      Module.finrank ℝ
          (affineSpan ℝ (face_set (polyhedron_le_set A b) c δ)).direction = n - 1 := by
    have hambient :
        Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction = n := by
      rw [hfull, AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
      simp
    rw [hambient] at hface_codim
    exact Nat.eq_sub_of_add_eq hface_codim
  have hker_finrank :
      Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) = n - 1 := by
    have hker_add_one :
        Module.finrank ℝ (LinearMap.ker (dotProductStrongDual c).toLinearMap) + 1 = n := by
      exact finrank_ker_dotProductStrongDual_add_one_eq hc_ne
    exact Nat.eq_sub_of_add_eq hker_add_one
  -- The face direction already sits inside the kernel, and the codimension computation shows the
  -- two subspaces have the same finite dimension.
  exact Submodule.eq_of_le_of_finrank_eq hdir_le (hface_finrank.trans hker_finrank.symm)

/-- Helper for Exercise 3.37: a linear functional is determined by its kernel together with one
transverse vector on which it evaluates to `1`. -/
lemma functional_eq_smul_of_eq_ker_and_eval_one
    {n : ℕ}
    {c d w : Fin n → ℝ}
    (hker_eq :
      LinearMap.ker (dotProductStrongDual c).toLinearMap =
        LinearMap.ker (dotProductStrongDual d).toLinearMap)
    (hw : c ⬝ᵥ w = 1) :
    d = (d ⬝ᵥ w) • c := by
  ext i
  let x : Fin n → ℝ := Pi.single i 1
  let x₀ : Fin n → ℝ := x - (c ⬝ᵥ x) • w
  have hx₀_mem_c :
      x₀ ∈ LinearMap.ker (dotProductStrongDual c).toLinearMap := by
    refine LinearMap.mem_ker.2 ?_
    -- The normalization subtracts the unique transverse component detected by `c`.
    dsimp [x₀]
    rw [dotProductStrongDual_apply, dotProduct_sub, dotProduct_smul, hw]
    ring
  have hx₀_mem_d :
      x₀ ∈ LinearMap.ker (dotProductStrongDual d).toLinearMap := by
    rw [← hker_eq]
    exact hx₀_mem_c
  have hx_split : x = x₀ + (c ⬝ᵥ x) • w := by
    ext j
    dsimp [x₀]
    ring
  have hd_eval :
      d ⬝ᵥ x = (c ⬝ᵥ x) * (d ⬝ᵥ w) := by
    have hx₀_eval_d : d ⬝ᵥ x₀ = 0 := by
      simpa [dotProductStrongDual_apply] using LinearMap.mem_ker.mp hx₀_mem_d
    -- The kernel part contributes nothing to `d`, so only the transverse component remains.
    calc
      d ⬝ᵥ x = d ⬝ᵥ (x₀ + (c ⬝ᵥ x) • w) := by
        simpa using congrArg (fun y ↦ d ⬝ᵥ y) hx_split
      _ = d ⬝ᵥ x₀ + d ⬝ᵥ ((c ⬝ᵥ x) • w) := by rw [dotProduct_add]
      _ = 0 + (c ⬝ᵥ x) * (d ⬝ᵥ w) := by
            simp [hx₀_eval_d, dotProduct_smul, smul_eq_mul]
      _ = (c ⬝ᵥ x) * (d ⬝ᵥ w) := by ring
  -- Evaluate the identity on the `i`th coordinate unit vector.
  simpa [x, dotProduct, Pi.single_apply, smul_eq_mul, mul_comm] using hd_eval

/-- Helper for Exercise 3.37: two nonzero valid inequalities cutting out the same facet of a
full-dimensional polyhedron are positive scalar multiples of one another. -/
lemma same_facet_valid_inequalities_pos_smul_of_full_dim
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c d : Fin n → ℝ}
    {δ ε : ℝ}
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hvalid_c : is_valid_inequality P c δ)
    (hvalid_d : is_valid_inequality P d ε)
    (hfacet : is_facet P (face_set P c δ))
    (hface : face_set P c δ = face_set P d ε)
    (hcd_ne : (c, δ) ≠ 0)
    (hde_ne : (d, ε) ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (d, ε) = t • (c, δ) := by
  have hfacet_d : is_facet P (face_set P d ε) := by
    simpa [hface] using hfacet
  obtain ⟨xF, hxF_face⟩ :=
    (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1
  have hxF_face_d : xF ∈ face_set P d ε := by
    simpa [hface] using hxF_face
  have hxF_eq_c : c ⬝ᵥ xF = δ := (mem_face_set_iff.mp hxF_face).2
  have hxF_eq_d : d ⬝ᵥ xF = ε := (mem_face_set_iff.mp hxF_face_d).2
  have hc_ne : c ≠ 0 := by
    intro hc
    have hδ_zero : δ = 0 := by simpa [hc, dotProduct] using hxF_eq_c.symm
    exact hcd_ne (by ext <;> simp [hc, hδ_zero])
  have hd_ne : d ≠ 0 := by
    intro hd
    have hε_zero : ε = 0 := by simpa [hd, dotProduct] using hxF_eq_d.symm
    exact hde_ne (by ext <;> simp [hd, hε_zero])
  have hker_c :
      (affineSpan ℝ (face_set P c δ)).direction =
        LinearMap.ker (dotProductStrongDual c).toLinearMap :=
    common_facet_direction_eq_kernel_of_valid_inequality hpolyhedron hfull hvalid_c hfacet hcd_ne
  have hker_d :
      (affineSpan ℝ (face_set P d ε)).direction =
        LinearMap.ker (dotProductStrongDual d).toLinearMap :=
    common_facet_direction_eq_kernel_of_valid_inequality hpolyhedron hfull hvalid_d hfacet_d hde_ne
  have hker_eq :
      LinearMap.ker (dotProductStrongDual c).toLinearMap =
        LinearMap.ker (dotProductStrongDual d).toLinearMap := by
    calc
      LinearMap.ker (dotProductStrongDual c).toLinearMap
          = (affineSpan ℝ (face_set P c δ)).direction := hker_c.symm
      _ = (affineSpan ℝ (face_set P d ε)).direction := by simpa [hface]
      _ = LinearMap.ker (dotProductStrongDual d).toLinearMap := hker_d
  have hface_ssubset :=
    (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.2.2
  have hx0_exists : ∃ x0 : Fin n → ℝ, x0 ∈ P ∧ x0 ∉ face_set P c δ := by
    exact Set.not_subset.mp hface_ssubset
  rcases hx0_exists with ⟨x0, hx0P, hx0_not_face⟩
  have hgap_pos :=
    outside_point_gap_pos_of_same_facet hvalid_c hvalid_d hface hx0P hx0_not_face
  set gc : ℝ := δ - c ⬝ᵥ x0 with hgc_def
  set gd : ℝ := ε - d ⬝ᵥ x0 with hgd_def
  have hgc_pos : 0 < gc := hgap_pos.1
  have hgd_pos : 0 < gd := hgap_pos.2
  let w : Fin n → ℝ := gc⁻¹ • (xF - x0)
  have hw_c : c ⬝ᵥ w = 1 := by
    -- Normalize the outside-point gap for `c` so the transverse vector evaluates to `1`.
    calc
      c ⬝ᵥ w = gc⁻¹ * (c ⬝ᵥ (xF - x0)) := by
        simp [w, dotProduct_smul]
      _ = gc⁻¹ * (δ - c ⬝ᵥ x0) := by rw [dotProduct_sub, hxF_eq_c]
      _ = 1 := by
        rw [← hgc_def]
        field_simp [ne_of_gt hgc_pos]
  have hd_eq : d = (d ⬝ᵥ w) • c :=
    functional_eq_smul_of_eq_ker_and_eval_one hker_eq hw_c
  have hε_eq : ε = (d ⬝ᵥ w) * δ := by
    have hd_eq_xF : d ⬝ᵥ xF = ((d ⬝ᵥ w) • c) ⬝ᵥ xF := by
      simpa using congrArg (fun v ↦ v ⬝ᵥ xF) hd_eq
    calc
      ε = d ⬝ᵥ xF := hxF_eq_d.symm
      _ = ((d ⬝ᵥ w) • c) ⬝ᵥ xF := hd_eq_xF
      _ = (d ⬝ᵥ w) * (c ⬝ᵥ xF) := by simp [dotProduct_smul]
      _ = (d ⬝ᵥ w) * δ := by rw [hxF_eq_c]
  have hgd_eq : gd = (d ⬝ᵥ w) * gc := by
    have hd_eq_x0 : d ⬝ᵥ x0 = ((d ⬝ᵥ w) • c) ⬝ᵥ x0 := by
      simpa using congrArg (fun v ↦ v ⬝ᵥ x0) hd_eq
    calc
      gd = ε - d ⬝ᵥ x0 := hgd_def
      _ = (d ⬝ᵥ w) * δ - d ⬝ᵥ x0 := by rw [hε_eq]
      _ = (d ⬝ᵥ w) * δ - ((d ⬝ᵥ w) • c) ⬝ᵥ x0 := by rw [hd_eq_x0]
      _ = (d ⬝ᵥ w) * δ - ((d ⬝ᵥ w) * (c ⬝ᵥ x0)) := by simp [dotProduct_smul]
      _ = (d ⬝ᵥ w) * gc := by
            rw [hgc_def]
            ring
  have ht_pos : 0 < d ⬝ᵥ w := by
    have hgc_nonneg : 0 ≤ gc := le_of_lt hgc_pos
    have htw_nonneg : 0 ≤ d ⬝ᵥ w := by
      by_contra hneg
      have hnonpos : d ⬝ᵥ w ≤ 0 := (lt_of_not_ge hneg).le
      have : gd ≤ 0 := by
        rw [hgd_eq]
        exact mul_nonpos_of_nonpos_of_nonneg hnonpos hgc_nonneg
      exact not_le_of_gt hgd_pos this
    have htw_ne_zero : d ⬝ᵥ w ≠ 0 := by
      intro hzero
      have : gd = 0 := by simpa [hzero] using hgd_eq
      exact (ne_of_gt hgd_pos) this
    exact lt_of_le_of_ne htw_nonneg htw_ne_zero.symm
  refine ⟨d ⬝ᵥ w, ht_pos, ?_⟩
  refine Prod.ext ?_ ?_
  · exact hd_eq
  · simpa [smul_eq_mul] using hε_eq

/-- Helper for Exercise 3.37: a tight lifted vertex row is a zero-slope row of the homogenized
system, so Exercise 3.27 places it in the span of the selected active independent rows. -/
lemma tight_vertex_row_mem_span_selected_rows_of_zero_slope
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    {α : Fin n → ℝ}
    {β : ℝ}
    {I : Fin n ↪ Fin (p + q)}
    (hI_active :
      ∀ k : Fin n,
        ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β)) (I k) = 0)
    (hI_linearIndependent :
      LinearIndependent ℝ
        (fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k)))
    (hαβ_ne : (α, β) ≠ 0)
    {i : Fin p}
    (hi : (α ᵥ* V) i = β) :
    ((vertexRayLiftedMatrix V R).transpose (finSumFinEquiv (Sum.inl i))) ∈
      Submodule.span ℝ
        (Set.range fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k)) := by
  let A : Matrix (Fin (p + q)) (Fin (n + 1)) ℝ := (vertexRayLiftedMatrix V R).transpose
  let rbar : Fin (n + 1) → ℝ := Fin.snoc α (-β)
  have hrbar_ne : rbar ≠ 0 := by
    intro hrbar_zero
    apply hαβ_ne
    simpa [rbar, liftedToSignedPair, signedPairToLifted] using congrArg liftedToSignedPair hrbar_zero
  have hi_active : (A *ᵥ rbar) (finSumFinEquiv (Sum.inl i)) = 0 := by
    -- Convert tightness of the listed vertex into an active row of the lifted system.
    simpa [A, rbar] using (lifted_vertex_row_active_iff V R α β i).2 hi
  -- Exercise 3.27 supplies the source-faithful span statement for every zero-slope row.
  simpa [A, rbar] using
    zeroSlopeRow_mem_span_selectedRows A hrbar_ne I hI_active hI_linearIndependent hi_active

/-- Helper for Exercise 3.37: if all selected active rows are lifted ray rows, then every vector in
their span has last coordinate `0`. -/
lemma last_coordinate_zero_on_span_of_selected_ray_rows
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    {I : Fin n ↪ Fin (p + q)}
    (hI_is_ray : ∀ k : Fin n, ∃ j : Fin q, I k = finSumFinEquiv (Sum.inr j))
    {x : Fin (n + 1) → ℝ}
    (hx :
      x ∈ Submodule.span ℝ
        (Set.range fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k))) :
    x (Fin.last n) = 0 := by
  let evalLast : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun y ↦ y (Fin.last n)
      map_add' := by
        intro y z
        simp
      map_smul' := by
        intro a y
        simp }
  have hspan_le : Submodule.span ℝ
      (Set.range fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k)) ≤
        LinearMap.ker evalLast := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    rcases hI_is_ray k with ⟨j, hj⟩
    refine LinearMap.mem_ker.2 ?_
    -- Every selected ray row has last coordinate `0`, so the whole span stays in that kernel.
    simpa [evalLast, hj] using lifted_ray_row_last_coordinate V R j
  exact LinearMap.mem_ker.mp (hspan_le hx)

/-- Helper for Exercise 3.37: among `n` selected active independent lifted rows at
`Fin.snoc α (-β)`, at least one row must be a lifted vertex row when some listed vertex is tight.
-/
lemma selected_active_rows_contain_vertex_anchor
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    {α : Fin n → ℝ}
    {β : ℝ}
    {I : Fin n ↪ Fin (p + q)}
    (hI_active :
      ∀ k : Fin n,
        ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β)) (I k) = 0)
    (hI_linearIndependent :
      LinearIndependent ℝ
        (fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k)))
    (hαβ_ne : (α, β) ≠ 0)
    (htight : ∃ i : Fin p, (α ᵥ* V) i = β) :
    ∃ k0 : Fin n, ∃ i0 : Fin p, I k0 = finSumFinEquiv (Sum.inl i0) := by
  by_contra hno_vertex
  have hI_is_ray : ∀ k : Fin n, ∃ j : Fin q, I k = finSumFinEquiv (Sum.inr j) := by
    intro k
    -- If a selected row were a vertex row, it would contradict the no-anchor assumption.
    cases hsplit : finSumFinEquiv.symm (I k) with
    | inl i =>
        have hk : I k = finSumFinEquiv (Sum.inl i) := by
          simpa using congrArg finSumFinEquiv hsplit
        exact False.elim (hno_vertex ⟨k, i, hk⟩)
    | inr j =>
        exact ⟨j, by simpa using congrArg finSumFinEquiv hsplit⟩
  rcases htight with ⟨i, hi⟩
  have hrow_mem :
      ((vertexRayLiftedMatrix V R).transpose (finSumFinEquiv (Sum.inl i))) ∈
        Submodule.span ℝ
          (Set.range fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k)) :=
    tight_vertex_row_mem_span_selected_rows_of_zero_slope
      V R hI_active hI_linearIndependent hαβ_ne hi
  have hlast_zero :
      ((vertexRayLiftedMatrix V R).transpose (finSumFinEquiv (Sum.inl i))) (Fin.last n) = 0 :=
    last_coordinate_zero_on_span_of_selected_ray_rows V R hI_is_ray hrow_mem
  have hlast_one :
      ((vertexRayLiftedMatrix V R).transpose (finSumFinEquiv (Sum.inl i))) (Fin.last n) = 1 :=
    lifted_vertex_row_last_coordinate V R i
  linarith

/-- Helper for Exercise 3.37: the canonical `succAbove` complement skips the anchored row `k0`. -/
lemma anchored_skip_ne_anchor_succAbove
    {n : ℕ}
    {k0 : Fin n}
    (t : Fin (n - 1)) :
    let hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
    let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
    let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
    skip t ≠ k0 := by
  dsimp
  have hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
  let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
  -- Route correction: the omitted index is the canonical complement of `k0`, not an arbitrary
  -- injection, so `succAbove` gives the exclusion proof directly.
  intro hskip
  have hpivot :
      pivot.succAboveEmb t = pivot := by
    apply Fin.cast_injective hn_cast
    simpa [skip, pivot] using hskip
  exact Fin.succAbove_ne pivot t hpivot

/-- Helper for Exercise 3.37: after anchoring at the selected vertex row `k0`, every remaining
selected lifted row has last coordinate `0`; deleting the last coordinate is therefore reversed by
`Fin.snoc · 0`. -/
lemma anchored_selected_row_eq_snoc_projection_succAbove
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    {I : Fin n ↪ Fin (p + q)}
    {k0 : Fin n}
    {i0 : Fin p}
    (hk0 : I k0 = finSumFinEquiv (Sum.inl i0))
    (t : Fin (n - 1)) :
    let hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
    let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
    let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
    let u : Fin n → Fin (n + 1) → ℝ :=
      fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
    let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
      fun s ↦ u (skip s) - (u (skip s)) (Fin.last n) • u k0
    let w : Fin (n - 1) → Fin n → ℝ :=
      fun s i ↦ z s i.castSucc
    z t (Fin.last n) = 0 ∧ Fin.snoc (w t) 0 = z t := by
  have hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
  let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
  let u : Fin n → Fin (n + 1) → ℝ := fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
  let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
    fun s ↦ u (skip s) - (u (skip s)) (Fin.last n) • u k0
  let w : Fin (n - 1) → Fin n → ℝ := fun s i ↦ z s i.castSucc
  have hk0_last : u k0 (Fin.last n) = 1 := by
    -- The anchor row is a lifted vertex row, so its homogenizing coordinate is `1`.
    simpa [u, hk0] using lifted_vertex_row_last_coordinate V R i0
  have hz_last : z t (Fin.last n) = 0 := by
    -- Route correction: split the selected non-anchor row into the vertex/ray cases, then use the
    -- anchor's last coordinate `1` to normalize away the last coordinate.
    cases hsplit : finSumFinEquiv.symm (I (skip t)) with
    | inl i =>
        have hrow :
            u (skip t) (Fin.last n) = 1 := by
          have hIt : I (skip t) = finSumFinEquiv (Sum.inl i) := by
            simpa using congrArg finSumFinEquiv hsplit
          simpa [u, hIt] using lifted_vertex_row_last_coordinate V R i
        simp [z, hrow, hk0_last]
    | inr j =>
        have hrow :
            u (skip t) (Fin.last n) = 0 := by
          have hIt : I (skip t) = finSumFinEquiv (Sum.inr j) := by
            simpa using congrArg finSumFinEquiv hsplit
          simpa [u, hIt] using lifted_ray_row_last_coordinate V R j
        simp [z, hrow, hk0_last]
  refine ⟨hz_last, ?_⟩
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [w]
  · simpa using hz_last.symm

/-- Helper for Exercise 3.37: inserting the compensating anchor coefficient at `pivot` rewrites a
linear combination of anchored differences back as a linear combination of the full family. -/
lemma insertNth_sum_smul_eq_sum_anchored_differences
    {m : ℕ}
    {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (pivot : Fin (m + 1))
    (u : Fin (m + 1) → E)
    (a c : Fin m → ℝ) :
    let d : Fin (m + 1) → ℝ := Fin.insertNth pivot (-∑ t, c t * a t) c
    ∑ k : Fin (m + 1), d k • u k =
      ∑ t : Fin m, c t • (u (pivot.succAbove t) - a t • u pivot) := by
  let d : Fin (m + 1) → ℝ := Fin.insertNth pivot (-∑ t, c t * a t) c
  change ∑ k : Fin (m + 1), d k • u k =
      ∑ t : Fin m, c t • (u (pivot.succAbove t) - a t • u pivot)
  -- Split the full sum at the anchored index, then absorb the anchor coefficient into the
  -- anchored-difference summands.
  calc
    ∑ k : Fin (m + 1), d k • u k
        = (-∑ t : Fin m, c t * a t) • u pivot + ∑ t : Fin m, c t • u (pivot.succAbove t) := by
            simpa [d] using
              (Fin.sum_univ_succAbove
                (f := fun k : Fin (m + 1) ↦ d k • u k)
                pivot)
    _
        = (∑ t : Fin m, (-(c t * a t)) • u pivot) + ∑ t : Fin m, c t • u (pivot.succAbove t) := by
            congr 1
            rw [show (-∑ t : Fin m, c t * a t) = ∑ t : Fin m, -(c t * a t) by
              simp [Finset.sum_neg_distrib], Finset.sum_smul]
    _ = ∑ t : Fin m, ((-(c t * a t)) • u pivot + c t • u (pivot.succAbove t)) := by
          rw [← Finset.sum_add_distrib]
    _ = ∑ t : Fin m, c t • (u (pivot.succAbove t) - a t • u pivot) := by
          refine Finset.sum_congr rfl ?_
          intro t ht
          rw [sub_eq_add_neg, smul_add, smul_neg, smul_smul]
          simp [mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc]

/-- Helper for Exercise 3.37: after anchoring the selected lifted rows at a selected vertex row,
deleting the last coordinate along the canonical `succAbove` complement preserves linear
independence. -/
lemma anchored_active_rows_linearIndependent_after_projection_succAbove
    {n p q : ℕ}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    {I : Fin n ↪ Fin (p + q)}
    {k0 : Fin n}
    {i0 : Fin p}
    (hk0 : I k0 = finSumFinEquiv (Sum.inl i0))
    (hI_linearIndependent :
      LinearIndependent ℝ
        (fun k : Fin n ↦ (vertexRayLiftedMatrix V R).transpose (I k))) :
    let hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
    let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
    let skip : Fin (n - 1) → Fin n := fun t ↦ Fin.cast hn_cast (pivot.succAboveEmb t)
    let u : Fin n → Fin (n + 1) → ℝ :=
      fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
    let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
      fun t ↦ u (skip t) - (u (skip t)) (Fin.last n) • u k0
    let w : Fin (n - 1) → Fin n → ℝ :=
      fun t i ↦ z t i.castSucc
    LinearIndependent ℝ w := by
  have hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
  let skip : Fin (n - 1) → Fin n := fun t ↦ Fin.cast hn_cast (pivot.succAboveEmb t)
  let u : Fin n → Fin (n + 1) → ℝ := fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
  let u' : Fin ((n - 1) + 1) → Fin (n + 1) → ℝ := fun k ↦ u (Fin.cast hn_cast k)
  let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
    fun t ↦ u (skip t) - (u (skip t)) (Fin.last n) • u k0
  let w : Fin (n - 1) → Fin n → ℝ := fun t i ↦ z t i.castSucc
  have hu' : LinearIndependent ℝ u' := by
    -- Reindex the selected lifted rows along the canonical cast `Fin ((n - 1) + 1) ≃ Fin n`.
    simpa [u'] using hI_linearIndependent.comp (Fin.cast hn_cast) (Fin.cast_injective hn_cast)
  rw [Fintype.linearIndependent_iff]
  intro f hfg t
  have hsnoc :
      ∑ s : Fin (n - 1), f s • Fin.snoc (w s) 0 = 0 := by
    -- Compare the lifted sums coordinatewise: the cast-succ coordinates come from `hfg`, and the
    -- last coordinate is zero on both sides.
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have hij := congrArg (fun y : Fin n → ℝ ↦ y j) hfg
      simpa [w, Fin.snoc] using hij
    · simp
  have hz :
      ∑ s : Fin (n - 1), f s • z s = 0 := by
    -- Replace each lifted `Fin.snoc (w s) 0` with the anchored row `z s`.
    have hsum_eq :
        ∑ s : Fin (n - 1), f s • z s =
          ∑ s : Fin (n - 1), f s • Fin.snoc (w s) 0 := by
      refine Finset.sum_congr rfl ?_
      intro s hs
      rcases anchored_selected_row_eq_snoc_projection_succAbove V R hk0 s with ⟨_, hsz⟩
      rw [hsz]
    rw [hsum_eq]
    exact hsnoc
  let af : Fin (n - 1) → ℝ := fun s ↦ (u' (pivot.succAbove s)) (Fin.last n)
  let df : Fin ((n - 1) + 1) → ℝ := Fin.insertNth pivot (-∑ s, f s * af s) f
  have hfull :
      ∑ k : Fin ((n - 1) + 1), df k • u' k = 0 := by
    -- Route correction: lift the projected relation to the full selected-row family via the
    -- canonical `Fin.insertNth` coefficient family at the anchor `pivot`.
    calc
      ∑ k : Fin ((n - 1) + 1), df k • u' k
          = ∑ s : Fin (n - 1), f s • (u' (pivot.succAbove s) - af s • u' pivot) := by
              simpa [df, af, u', z, skip, pivot, hn_cast, Fin.cast_eq_self] using
                insertNth_sum_smul_eq_sum_anchored_differences pivot u' af f
      _ = 0 := by
            simpa [af, u', z, skip, pivot, hn_cast, Fin.cast_eq_self] using hz
  have hcoeff := (Fintype.linearIndependent_iff.mp hu' df hfull) (pivot.succAbove t)
  simpa [df] using hcoeff

/-- Helper for Exercise 3.37: a recession direction with zero slope at a point of the equality
face lies in the direction space of that face. -/
lemma recession_direction_mem_faceSet_direction
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {α x0 r : Fin n → ℝ}
    {β : ℝ}
    (hx0 : x0 ∈ face_set P α β)
    (hr : r ∈ recessionCone P)
    (hzero : α ⬝ᵥ r = 0) :
    r ∈ (affineSpan ℝ (face_set P α β)).direction := by
  have hx0P : x0 ∈ P := (mem_face_set_iff.mp hx0).1
  have hx0_eq : α ⬝ᵥ x0 = β := (mem_face_set_iff.mp hx0).2
  have hx0_add_mem : x0 + r ∈ P := by
    -- Move one step along the recession direction from the face point.
    simpa using (mem_recessionCone_iff.mp hr) hx0P 1 zero_le_one
  have hx0_add_face : x0 + r ∈ face_set P α β := by
    -- The zero-slope hypothesis keeps the translate on the same supporting hyperplane.
    refine (mem_face_set_iff).2 ⟨hx0_add_mem, ?_⟩
    calc
      α ⬝ᵥ (x0 + r) = α ⬝ᵥ x0 + α ⬝ᵥ r := by
        simp [dotProduct_add]
      _ = β + 0 := by rw [hx0_eq, hzero]
      _ = β := by ring
  -- The direction space is generated by differences of points in the affine span of the face.
  simpa [vsub_eq_sub] using
    (AffineSubspace.vsub_mem_direction
      (subset_affineSpan ℝ (face_set P α β) hx0_add_face)
      (subset_affineSpan ℝ (face_set P α β) hx0))

/-- Helper for Exercise 3.37: each projected anchored active lifted row is a direction of the
equality face `face_set P α β`. -/
lemma projected_normalized_selected_row_mem_faceSet_direction_succAbove
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    {I : Fin n ↪ Fin (p + q)}
    (hI_active :
      ∀ k : Fin n,
        ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β)) (I k) = 0)
    {k0 : Fin n}
    {i0 : Fin p}
    (hk0 : I k0 = finSumFinEquiv (Sum.inl i0))
    (t : Fin (n - 1)) :
    let hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
    let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
    let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
    let u : Fin n → Fin (n + 1) → ℝ :=
      fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
    let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
      fun s ↦ u (skip s) - (u (skip s)) (Fin.last n) • u k0
    let w : Fin (n - 1) → Fin n → ℝ :=
      fun s i ↦ z s i.castSucc
    w t ∈ (affineSpan ℝ (face_set P α β)).direction := by
  have hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
  let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
  let u : Fin n → Fin (n + 1) → ℝ := fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
  let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
    fun s ↦ u (skip s) - (u (skip s)) (Fin.last n) • u k0
  let w : Fin (n - 1) → Fin n → ℝ := fun s i ↦ z s i.castSucc
  have hk0_active :
      ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
          (finSumFinEquiv (Sum.inl i0)) = 0 := by
    simpa [hk0] using hI_active k0
  have hi0 : (α ᵥ* V) i0 = β :=
    (lifted_vertex_row_active_iff V R α β i0).1 hk0_active
  have hx0 : Vᵀ i0 ∈ face_set P α β := mem_faceSet_of_tightVertex hvertices hi0
  -- Route correction: consume the canonical `succAbove` row identity, then split into the
  -- tight-vertex difference case and the zero-slope recession-direction case.
  cases hsplit : finSumFinEquiv.symm (I (skip t)) with
  | inl i =>
      have hIt : I (skip t) = finSumFinEquiv (Sum.inl i) := by
        simpa using congrArg finSumFinEquiv hsplit
      have hi_active :
          ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
              (finSumFinEquiv (Sum.inl i)) = 0 := by
        simpa [hIt] using hI_active (skip t)
      have hi : (α ᵥ* V) i = β :=
        (lifted_vertex_row_active_iff V R α β i).1 hi_active
      have hxi : Vᵀ i ∈ face_set P α β := mem_faceSet_of_tightVertex hvertices hi
      have hrow_explicit :
          (fun s ↦
            (vertexRayLiftedMatrix V R).transpose (I (skip t)) s.castSucc -
              (vertexRayLiftedMatrix V R).transpose (I (skip t)) (Fin.last n) *
                (vertexRayLiftedMatrix V R).transpose (I k0) s.castSucc) =
            Vᵀ i - Vᵀ i0 := by
        ext s
        simp [hIt, hk0, vertexRayLiftedMatrix, Fin.lastCases]
      have hrow : w t = Vᵀ i - Vᵀ i0 := by
        simpa [w, z, u] using hrow_explicit
      have hdir :
          Vᵀ i - Vᵀ i0 ∈ (affineSpan ℝ (face_set P α β)).direction := by
        -- Two tight vertices determine a direction of the common equality face.
        simpa [vsub_eq_sub] using
          (AffineSubspace.vsub_mem_direction
            (subset_affineSpan ℝ (face_set P α β) hxi)
            (subset_affineSpan ℝ (face_set P α β) hx0))
      have hdir_explicit :
          (fun s ↦
            (vertexRayLiftedMatrix V R).transpose (I (skip t)) s.castSucc -
              (vertexRayLiftedMatrix V R).transpose (I (skip t)) (Fin.last n) *
                (vertexRayLiftedMatrix V R).transpose (I k0) s.castSucc) ∈
            (affineSpan ℝ (face_set P α β)).direction := by
        rwa [hrow_explicit]
      simpa [w, z, u] using hdir_explicit
  | inr j =>
      have hIt : I (skip t) = finSumFinEquiv (Sum.inr j) := by
        simpa using congrArg finSumFinEquiv hsplit
      have hj_active :
          ((vertexRayLiftedMatrix V R).transpose *ᵥ Fin.snoc α (-β))
              (finSumFinEquiv (Sum.inr j)) = 0 := by
        simpa [hIt] using hI_active (skip t)
      have hj_zero : (α ᵥ* R) j = 0 :=
        (lifted_ray_row_active_iff V R α β j).1 hj_active
      have hray : Rᵀ j ∈ recessionCone P :=
        isExtremeRayOfPointedPolyhedron_mem_recessionCone (hrays j)
      have hrow_explicit :
          (fun s ↦
            (vertexRayLiftedMatrix V R).transpose (I (skip t)) s.castSucc -
              (vertexRayLiftedMatrix V R).transpose (I (skip t)) (Fin.last n) *
                (vertexRayLiftedMatrix V R).transpose (I k0) s.castSucc) =
            Rᵀ j := by
        ext s
        simp [hIt, hk0, vertexRayLiftedMatrix, Fin.lastCases]
      have hrow : w t = Rᵀ j := by
        simpa [w, z, u] using hrow_explicit
      have hdir : Rᵀ j ∈ (affineSpan ℝ (face_set P α β)).direction :=
        recession_direction_mem_faceSet_direction hx0 hray
          (by simpa [Matrix.vecMul, dotProduct] using hj_zero)
      have hdir_explicit :
          (fun s ↦
            (vertexRayLiftedMatrix V R).transpose (I (skip t)) s.castSucc -
              (vertexRayLiftedMatrix V R).transpose (I (skip t)) (Fin.last n) *
                (vertexRayLiftedMatrix V R).transpose (I k0) s.castSucc) ∈
            (affineSpan ℝ (face_set P α β)).direction := by
        rwa [hrow_explicit]
      simpa [w, z, u] using hdir_explicit

/-- Helper for Exercise 3.37: an extreme ray together with a tight listed vertex produces
`n - 1` linearly independent directions inside the equality face. -/
lemma anchored_active_rows_give_face_direction_family
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    (hExtreme : IsExtremeRayOfCone (vertex_ray_dual_cone V R) (α, β))
    (htight : ∃ i : Fin p, (α ᵥ* V) i = β) :
    ∃ w : Fin (n - 1) → Fin n → ℝ,
      LinearIndependent ℝ w ∧
        ∀ t : Fin (n - 1), w t ∈ (affineSpan ℝ (face_set P α β)).direction := by
  have hαβ_ne : (α, β) ≠ 0 := extremeRay_ne_zero hExtreme
  obtain ⟨I, hI_active, hI_linearIndependent⟩ :=
    lifted_dual_cone_extreme_ray_exists_active_linearlyIndependent_rows
      V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hExtreme
  obtain ⟨k0, i0, hk0⟩ :=
    selected_active_rows_contain_vertex_anchor
      V R hI_active hI_linearIndependent hαβ_ne htight
  have hn_cast : (n - 1) + 1 = n := fin_sub_one_add_one_eq k0
  let pivot : Fin ((n - 1) + 1) := Fin.cast hn_cast.symm k0
  let skip : Fin (n - 1) → Fin n := fun s ↦ Fin.cast hn_cast (pivot.succAboveEmb s)
  let u : Fin n → Fin (n + 1) → ℝ := fun k ↦ (vertexRayLiftedMatrix V R).transpose (I k)
  let z : Fin (n - 1) → Fin (n + 1) → ℝ :=
    fun s ↦ u (skip s) - (u (skip s)) (Fin.last n) • u k0
  let w : Fin (n - 1) → Fin n → ℝ := fun s i ↦ z s i.castSucc
  refine ⟨w, ?_, ?_⟩
  · -- The anchored `succAbove` projection preserves the selected-row independence.
    simpa [w, z, u, skip, pivot, hn_cast] using
      (anchored_active_rows_linearIndependent_after_projection_succAbove
        V R hk0 hI_linearIndependent)
  · intro t
    -- Each projected row is already identified as a direction of the equality face.
    simpa [w, z, u, skip, pivot, hn_cast] using
      (projected_normalized_selected_row_mem_faceSet_direction_succAbove
        V R hvertices hrays hI_active hk0 t)

/-- Helper for Exercise 3.37: an extreme ray of the lifted dual cone that is tight on a listed
vertex cuts out a codimension-one equality face. -/
lemma faceSet_codim_of_extremeRay_and_tightVertex
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β : ℝ}
    (hExtreme : IsExtremeRayOfCone (vertex_ray_dual_cone V R) (α, β))
    (htight : ∃ i : Fin p, (α ᵥ* V) i = β) :
    Module.finrank ℝ (affineSpan ℝ (face_set P α β)).direction + 1 =
      Module.finrank ℝ (affineSpan ℝ P).direction := by
  rcases htight with ⟨i0, hi0⟩
  have hx0 : Vᵀ i0 ∈ face_set P α β := mem_faceSet_of_tightVertex hvertices hi0
  obtain ⟨w, hw_linearIndependent, hw_mem⟩ :=
    anchored_active_rows_give_face_direction_family
      V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hExtreme ⟨i0, hi0⟩
  let S : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ (Set.range w)
  have hS_le : S ≤ (affineSpan ℝ (face_set P α β)).direction := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    exact hw_mem t
  have hS_finrank : Module.finrank ℝ S = n - 1 := by
    -- The anchored family contributes `n - 1` independent face directions.
    simpa [S] using finrank_span_eq_card (R := ℝ) (b := w) hw_linearIndependent
  have hdir_lower :
      n - 1 ≤ Module.finrank ℝ (affineSpan ℝ (face_set P α β)).direction := by
    simpa [hS_finrank] using (Submodule.finrank_mono hS_le)
  have hα_ne : α ≠ 0 := by
    have hαβ_ne : (α, β) ≠ 0 := extremeRay_ne_zero hExtreme
    intro hα_zero
    have hβ_zero : β = 0 := by
      simpa [hα_zero, Matrix.vecMul, dotProduct] using hi0.symm
    exact hαβ_ne (by ext <;> simp [hα_zero, hβ_zero])
  have hdir_le :
      (affineSpan ℝ (face_set P α β)).direction ≤
        LinearMap.ker (dotProductStrongDual α).toLinearMap :=
    face_set_direction_le_dotProduct_ker hx0
  have hker_finrank :
      Module.finrank ℝ (LinearMap.ker (dotProductStrongDual α).toLinearMap) = n - 1 := by
    have hker_add_one :
        Module.finrank ℝ (LinearMap.ker (dotProductStrongDual α).toLinearMap) + 1 = n := by
      exact finrank_ker_dotProductStrongDual_add_one_eq hα_ne
    exact Nat.eq_sub_of_add_eq hker_add_one
  have hdir_upper :
      Module.finrank ℝ (affineSpan ℝ (face_set P α β)).direction ≤ n - 1 := by
    simpa [hker_finrank] using (Submodule.finrank_mono hdir_le)
  have hdir_finrank :
      Module.finrank ℝ (affineSpan ℝ (face_set P α β)).direction = n - 1 :=
    le_antisymm hdir_upper hdir_lower
  have hambient :
      Module.finrank ℝ (affineSpan ℝ P).direction = n := by
    rw [hfull, AffineSubspace.direction_top, finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  have hn_pos : 0 < n := fin_dim_pos_of_ne_zero_vector hα_ne
  rw [hdir_finrank, hambient]
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt hn_pos)

/-- Helper for Exercise 3.37: a facet-defining inequality cannot have zero coefficient pair,
because the zero pair cuts out all of `P` rather than a proper face. -/
lemma pair_ne_zero_of_facet_defining_inequality
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {α : Fin n → ℝ}
    {β : ℝ}
    (hfacet : facet_defining_inequality P α β) :
    (α, β) ≠ 0 := by
  have hssubset :
      face_set P α β ⊂ P :=
    (is_proper_face_iff.mp
      (is_facet_to_is_proper_face (facet_defining_inequality_is_facet hfacet))).2.2
  intro hzero
  cases hzero
  -- The zero inequality exposes the whole polyhedron, contradicting facet properness.
  have hface_all : face_set P (0 : Fin n → ℝ) 0 = P := by
    ext x
    simp [mem_face_set_iff, dotProduct]
  exact hssubset.ne hface_all

/-- Helper for Exercise 3.37: scaling a valid inequality by a nonnegative scalar preserves
validity. -/
lemma valid_inequality_smul_nonneg
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c : Fin n → ℝ}
    {δ t : ℝ}
    (hvalid : is_valid_inequality P c δ)
    (ht : 0 ≤ t) :
    is_valid_inequality P (t • c) (t * δ) := by
  intro x hx
  -- Multiply the original inequality by the nonnegative scalar `t`.
  calc
    (t • c) ⬝ᵥ x = t * (c ⬝ᵥ x) := by
      simp [dotProduct, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ ≤ t * δ := mul_le_mul_of_nonneg_left (hvalid hx) ht

/-- Helper for Exercise 3.37: if a nonzero valid inequality defines a face containing a facet,
then that larger face must equal the facet. -/
lemma facet_face_eq_of_subset_of_valid_inequality_nonzero
    {n : ℕ}
    {P : Set (Fin n → ℝ)}
    {c d : Fin n → ℝ}
    {δ ε : ℝ}
    (hfull : affineSpan ℝ P = ⊤)
    (hfacet : is_facet P (face_set P c δ))
    (hvalid : is_valid_inequality P d ε)
    (hde_ne : (d, ε) ≠ 0)
    (hsub : face_set P c δ ⊆ face_set P d ε) :
    face_set P d ε = face_set P c δ := by
  obtain ⟨xF, hxF⟩ :=
    (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet)).2.1
  have hface_nonempty : (face_set P d ε).Nonempty := ⟨xF, hsub hxF⟩
  have hproper :
      is_proper_face P (face_set P d ε) :=
    proper_face_of_valid_inequality_of_nonzero_of_nonempty_of_affineSpan_eq_top
      hvalid hfull hde_ne hface_nonempty
  -- Maximality of the facet upgrades the face inclusion to equality.
  exact is_facet_maximal hfacet hproper hsub

/-- Helper for Exercise 3.37: each positive summand in a proper conic decomposition of a
facet-defining inequality exposes the same facet after scaling. -/
lemma decomposition_summand_faces_eq_facet
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β μ₁ μ₂ : ℝ}
    {u₁ u₂ : (Fin n → ℝ) × ℝ}
    (hfacet : facet_defining_inequality P α β)
    (hu₁ : u₁ ∈ vertex_ray_dual_cone V R)
    (hu₂ : u₂ ∈ vertex_ray_dual_cone V R)
    (hu₁_ne : u₁ ≠ 0)
    (hu₂_ne : u₂ ≠ 0)
    (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂)
    (hdecomp : (α, β) = μ₁ • u₁ + μ₂ • u₂) :
    face_set P (μ₁ • u₁.1) (μ₁ * u₁.2) = face_set P α β ∧
      face_set P (μ₂ • u₂.1) (μ₂ * u₂.2) = face_set P α β := by
  have hvalid : is_valid_inequality P α β := facet_defining_inequality_valid hfacet
  have hfacet_face : is_facet P (face_set P α β) := facet_defining_inequality_is_facet hfacet
  have hvalid_u₁ : is_valid_inequality P u₁.1 u₁.2 :=
    validInequality_of_mem_vertexRayDualCone
      hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hu₁
  have hvalid_u₂ : is_valid_inequality P u₂.1 u₂.2 :=
    validInequality_of_mem_vertexRayDualCone
      hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hu₂
  have hvalid_d₁ : is_valid_inequality P (μ₁ • u₁.1) (μ₁ * u₁.2) :=
    valid_inequality_smul_nonneg hvalid_u₁ (le_of_lt hμ₁)
  have hvalid_d₂ : is_valid_inequality P (μ₂ • u₂.1) (μ₂ * u₂.2) :=
    valid_inequality_smul_nonneg hvalid_u₂ (le_of_lt hμ₂)
  have hd₁_ne : (μ₁ • u₁.1, μ₁ * u₁.2) ≠ 0 := by
    intro hd₁_zero
    apply hu₁_ne
    have hsmul_zero : μ₁ • u₁ = 0 := by
      cases u₁
      simpa [smul_eq_mul] using hd₁_zero
    exact (smul_eq_zero.mp hsmul_zero).resolve_left hμ₁.ne'
  have hd₂_ne : (μ₂ • u₂.1, μ₂ * u₂.2) ≠ 0 := by
    intro hd₂_zero
    apply hu₂_ne
    have hsmul_zero : μ₂ • u₂ = 0 := by
      cases u₂
      simpa [smul_eq_mul] using hd₂_zero
    exact (smul_eq_zero.mp hsmul_zero).resolve_left hμ₂.ne'
  have hα :
      α = (μ₁ • u₁).1 + (μ₂ • u₂).1 := congrArg Prod.fst hdecomp
  have hβ :
      β = (μ₁ • u₁).2 + (μ₂ • u₂).2 := congrArg Prod.snd hdecomp
  have hsub₁ :
      face_set P α β ⊆ face_set P (μ₁ • u₁.1) (μ₁ * u₁.2) := by
    intro x hx
    have hx_sum :
        x ∈ face_set P ((μ₁ • u₁).1 + (μ₂ • u₂).1) ((μ₁ • u₁).2 + (μ₂ • u₂).2) := by
      simpa [hα, hβ] using hx
    -- Route correction: first split tightness across the two scaled summands, then use facet
    -- maximality to turn the resulting face inclusion into equality.
    exact (sum_tight_implies_component_tight hvalid_d₁ hvalid_d₂ hx_sum).1
  have hsub₂ :
      face_set P α β ⊆ face_set P (μ₂ • u₂.1) (μ₂ * u₂.2) := by
    intro x hx
    have hx_sum :
        x ∈ face_set P ((μ₁ • u₁).1 + (μ₂ • u₂).1) ((μ₁ • u₁).2 + (μ₂ • u₂).2) := by
      simpa [hα, hβ] using hx
    exact (sum_tight_implies_component_tight hvalid_d₁ hvalid_d₂ hx_sum).2
  refine
    ⟨facet_face_eq_of_subset_of_valid_inequality_nonzero hfull hfacet_face hvalid_d₁ hd₁_ne hsub₁,
      facet_face_eq_of_subset_of_valid_inequality_nonzero hfull hfacet_face hvalid_d₂ hd₂_ne
        hsub₂⟩

/-- Helper for Exercise 3.37: if a facet-defining inequality decomposes as a positive sum of two
dual-cone rays, then each summand lies on the same ray as the original pair. -/
lemma decomposition_summands_sameRay_of_facet
    {n p q : ℕ}
    {P : Set (Fin n → ℝ)}
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    {α : Fin n → ℝ}
    {β μ₁ μ₂ : ℝ}
    {u₁ u₂ : (Fin n → ℝ) × ℝ}
    (hfacet : facet_defining_inequality P α β)
    (hu₁ : u₁ ∈ vertex_ray_dual_cone V R)
    (hu₂ : u₂ ∈ vertex_ray_dual_cone V R)
    (hu₁_ne : u₁ ≠ 0)
    (hu₂_ne : u₂ ≠ 0)
    (hμ₁ : 0 < μ₁)
    (hμ₂ : 0 < μ₂)
    (hdecomp : (α, β) = μ₁ • u₁ + μ₂ • u₂) :
    SameRay ℝ u₁ (α, β) ∧ SameRay ℝ u₂ (α, β) := by
  have hvalid : is_valid_inequality P α β := facet_defining_inequality_valid hfacet
  have hfacet_face : is_facet P (face_set P α β) := facet_defining_inequality_is_facet hfacet
  have hαβ_ne : (α, β) ≠ 0 := pair_ne_zero_of_facet_defining_inequality hfacet
  have hvalid_u₁ : is_valid_inequality P u₁.1 u₁.2 :=
    validInequality_of_mem_vertexRayDualCone
      hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hu₁
  have hvalid_u₂ : is_valid_inequality P u₂.1 u₂.2 :=
    validInequality_of_mem_vertexRayDualCone
      hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hu₂
  have hvalid_d₁ : is_valid_inequality P (μ₁ • u₁.1) (μ₁ * u₁.2) :=
    valid_inequality_smul_nonneg hvalid_u₁ (le_of_lt hμ₁)
  have hvalid_d₂ : is_valid_inequality P (μ₂ • u₂.1) (μ₂ * u₂.2) :=
    valid_inequality_smul_nonneg hvalid_u₂ (le_of_lt hμ₂)
  have hd₁_ne : (μ₁ • u₁.1, μ₁ * u₁.2) ≠ 0 := by
    intro hd₁_zero
    apply hu₁_ne
    have hsmul_zero : μ₁ • u₁ = 0 := by
      cases u₁
      simpa [smul_eq_mul] using hd₁_zero
    exact (smul_eq_zero.mp hsmul_zero).resolve_left hμ₁.ne'
  have hd₂_ne : (μ₂ • u₂.1, μ₂ * u₂.2) ≠ 0 := by
    intro hd₂_zero
    apply hu₂_ne
    have hsmul_zero : μ₂ • u₂ = 0 := by
      cases u₂
      simpa [smul_eq_mul] using hd₂_zero
    exact (smul_eq_zero.mp hsmul_zero).resolve_left hμ₂.ne'
  obtain ⟨hface₁, hface₂⟩ :=
    decomposition_summand_faces_eq_facet
      V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep
      hfacet hu₁ hu₂ hu₁_ne hu₂_ne hμ₁ hμ₂ hdecomp
  obtain ⟨t₁, ht₁_pos, ht₁_eq⟩ :=
    same_facet_valid_inequalities_pos_smul_of_full_dim
      hpolyhedron hfull hvalid hvalid_d₁ hfacet_face hface₁.symm hαβ_ne hd₁_ne
  obtain ⟨t₂, ht₂_pos, ht₂_eq⟩ :=
    same_facet_valid_inequalities_pos_smul_of_full_dim
      hpolyhedron hfull hvalid hvalid_d₂ hfacet_face hface₂.symm hαβ_ne hd₂_ne
  have ht₁_eq' : μ₁ • u₁ = t₁ • (α, β) := by
    cases u₁
    simpa [smul_eq_mul] using ht₁_eq
  have ht₂_eq' : μ₂ • u₂ = t₂ • (α, β) := by
    cases u₂
    simpa [smul_eq_mul] using ht₂_eq
  have hs₁_scaled : SameRay ℝ (μ₁ • u₁) (α, β) := by
    rw [ht₁_eq']
    exact SameRay.sameRay_pos_smul_left (α, β) ht₁_pos
  have hs₂_scaled : SameRay ℝ (μ₂ • u₂) (α, β) := by
    rw [ht₂_eq']
    exact SameRay.sameRay_pos_smul_left (α, β) ht₂_pos
  have hs₁ : SameRay ℝ u₁ (α, β) :=
    SameRay.trans (SameRay.sameRay_pos_smul_right u₁ hμ₁) hs₁_scaled
      (fun hzero ↦ Or.inl ((smul_eq_zero.mp hzero).resolve_left hμ₁.ne'))
  have hs₂ : SameRay ℝ u₂ (α, β) :=
    SameRay.trans (SameRay.sameRay_pos_smul_right u₂ hμ₂) hs₂_scaled
      (fun hzero ↦ Or.inl ((smul_eq_zero.mp hzero).resolve_left hμ₂.ne'))
  exact ⟨hs₁, hs₂⟩

/-- Exercise 3.37. Let `P ⊆ ℝ^n` be a full-dimensional pointed polyhedron, and let the columns of
`V` and `R` list its vertices and extreme rays, respectively, with `Rᵀ` a representative family
up to `SameRay ℝ`. Then `P` is the `x`-projection of the lifted polyhedron with variables
`(x, λ, μ)` cut out by `x - V λ - R μ = 0`, `0 ≤ λ`, `0 ≤ μ`, and `∑ i, λ i = 1`, as recorded by
the companion theorem `vertex_ray_polyhedron_eq_x_projection`. Moreover, an inequality `α · x ≤ β`
is facet-defining for `P` if and only if `(α, β)` generates an extreme ray of the pointed cone
`vertex_ray_dual_cone V R = {(α, β) | α ᵥ* V ≤ β, α ᵥ* R ≤ 0}` and is tight on at least one listed
vertex. -/
theorem facet_defining_iff_extreme_ray_of_vertex_ray_polyhedron
    {n p q : ℕ}
    (P : Set (Fin n → ℝ))
    (V : Matrix (Fin n) (Fin p) ℝ)
    (R : Matrix (Fin n) (Fin q) ℝ)
    (hpolyhedron : is_polyhedron P)
    (hfull : affineSpan ℝ P = ⊤)
    (hpointed : is_pointed P)
    (hvertices : Set.range Vᵀ = P.extremePoints ℝ)
    (hrays : ∀ j : Fin q, IsExtremeRayOfPointedPolyhedron P (Rᵀ j))
    (h_extreme_rep :
      ∀ r : Fin n → ℝ, IsExtremeRayOfPointedPolyhedron P r →
        ∃ j : Fin q, SameRay ℝ r (Rᵀ j))
    (α : Fin n → ℝ)
    (β : ℝ) :
    facet_defining_inequality P α β ↔
      IsExtremeRayOfCone (vertex_ray_dual_cone V R) (α, β) ∧
        ∃ i : Fin p, (α ᵥ* V) i = β := by
  constructor
  · intro hfacet
    have hvalid : is_valid_inequality P α β := facet_defining_inequality_valid hfacet
    have hdual : (α, β) ∈ vertex_ray_dual_cone V R :=
      mem_vertexRayDualCone_of_validInequality
        hfull hvertices hrays hvalid
    have hfacet_face : is_facet P (face_set P α β) :=
      facet_defining_inequality_is_facet hfacet
    have hαβ_ne : (α, β) ≠ 0 := pair_ne_zero_of_facet_defining_inequality hfacet
    obtain ⟨xF, hxF⟩ :=
      (is_proper_face_iff.mp (is_facet_to_is_proper_face hfacet_face)).2.1
    have htight : ∃ i : Fin p, (α ᵥ* V) i = β :=
      exists_tightVertex_of_faceSet_point
        V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hxF hdual
    refine ⟨?_, htight⟩
    refine
      (isExtremeRayOfCone_iff_not_proper_conic_combination_of_distinct_rays
        (vertex_ray_dual_cone_as_pointedCone V R) hdual hαβ_ne).2 ?_
    intro hproper
    rcases hproper with
      ⟨u₁, u₂, hu₁, hu₂, hu₁_ne, hu₂_ne, hnot_same, μ₁, μ₂, hμ₁, hμ₂, hdecomp⟩
    -- Route correction: follow the source decomposition argument by showing each positive summand
    -- exposes the same facet, hence each summand lies on the same ray as `(α, β)`.
    obtain ⟨hs₁, hs₂⟩ :=
      decomposition_summands_sameRay_of_facet
        V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep
        hfacet hu₁ hu₂ hu₁_ne hu₂_ne hμ₁ hμ₂ hdecomp
    exact hnot_same (SameRay.trans hs₁ hs₂.symm (fun hzero ↦ False.elim (hαβ_ne hzero)))
  · rintro ⟨hExtreme, htight⟩
    have hvalid : is_valid_inequality P α β :=
      validInequality_of_mem_vertexRayDualCone
        hpolyhedron hfull hpointed hvertices hrays h_extreme_rep
        (mem_vertexRayDualCone_of_isExtremeRay hExtreme)
    have hface_nonempty : (face_set P α β).Nonempty :=
      faceSet_nonempty_of_exists_tightVertex hvertices htight
    have hcodim :
        Module.finrank ℝ (affineSpan ℝ (face_set P α β)).direction + 1 =
          Module.finrank ℝ (affineSpan ℝ P).direction :=
      faceSet_codim_of_extremeRay_and_tightVertex
        V R hpolyhedron hfull hpointed hvertices hrays h_extreme_rep hExtreme htight
    rcases hpolyhedron with ⟨m, A, b, rfl⟩
    obtain ⟨x0, hx0face⟩ := hface_nonempty
    have hP_nonempty : (polyhedron_le_set A b).Nonempty := ⟨x0, (mem_face_set_iff.mp hx0face).1⟩
    have hface_nonempty' : (face_set (polyhedron_le_set A b) α β).Nonempty := by
      simpa using faceSet_nonempty_of_exists_tightVertex hvertices htight
    refine (facet_defining_inequality_iff).2 ⟨hvalid, ?_⟩
    exact
      (is_facet_iff_nonempty_finrank_direction_affineSpan_add_one_eq
        A b hP_nonempty (face_set (polyhedron_le_set A b) α β)
        (isExposed_face_set_of_valid_inequality hvalid)).2
        ⟨hface_nonempty', hcodim⟩

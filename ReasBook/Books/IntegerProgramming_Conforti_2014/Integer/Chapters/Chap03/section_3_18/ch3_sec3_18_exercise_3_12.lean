import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_proposition_3_15
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_theorem_3_22
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_definition_3_16_extra_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was unavailable in this environment; the declarations
-- below were matched against local Chapter 3 precedent for the polyhedron `{x | A *ᵥ x ≤ b}`,
-- together with mathlib's affine-span / orthogonal-complement interface.

/-- The polyhedron of row vectors that admit both a nonnegative and a nonpositive multiplier
representation with the same right-hand-side value on `b`. -/
def balanced_row_multiplier_polyhedron
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  {y : Fin n → ℝ |
    ∃ u v : Fin m → ℝ,
      0 ≤ u ∧ v ≤ 0 ∧ y = u ᵥ* A ∧ y = v ᵥ* A ∧ u ⬝ᵥ b = v ⬝ᵥ b}

/-- The canonical Euclidean realization of `Fin n → ℝ` has inner product given by dot product. -/
lemma inner_toEuclidean_eq_dotProduct
    {n : ℕ}
    (x y : Fin n → ℝ) :
    inner ℝ ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
        ((EuclideanSpace.equiv (Fin n) ℝ).symm y) =
      x ⬝ᵥ y := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

/-- In the canonical Euclidean realization of `ℝ^n`, orthogonality to a subspace is equivalent to
vanishing dot product on each vector of that subspace. -/
lemma mem_toEuclidean_orthogonal_iff_dotProduct_eq_zero
    {n : ℕ}
    (L : Submodule ℝ (Fin n → ℝ))
    (y : Fin n → ℝ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm y ∈ L.toEuclideanᗮ ↔
      ∀ z ∈ L, y ⬝ᵥ z = 0 := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  constructor
  · intro hy z hz
    have hz' : e z ∈ L.toEuclidean := Submodule.mem_map_of_mem hz
    have hyz : inner ℝ (e y) (e z) = 0 := (L.toEuclidean.mem_orthogonal' (e y)).1 hy _ hz'
    rw [show inner ℝ (e y) (e z) = y ⬝ᵥ z by
      simpa [e] using inner_toEuclidean_eq_dotProduct y z] at hyz
    exact hyz
  · intro hy
    rw [Submodule.mem_orthogonal']
    intro z hz
    rcases hz with ⟨w, hw, rfl⟩
    change inner ℝ (e y) (e w) = 0
    rw [show inner ℝ (e y) (e w) = y ⬝ᵥ w by
      simpa [e] using inner_toEuclidean_eq_dotProduct y w]
    exact hy w hw

/-- The direction of the affine span commutes with the canonical Euclidean realization of `ℝ^n`. -/
lemma direction_affineSpan_toEuclidean
    {n : ℕ}
    (S : Set (Fin n → ℝ)) :
    (affineSpan ℝ S.toEuclidean).direction = (affineSpan ℝ S).direction.toEuclidean := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  let f : (Fin n → ℝ) →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := e.toAffineEquiv.toAffineMap
  have hspan :
      affineSpan ℝ S.toEuclidean = (affineSpan ℝ S).map f := by
    change affineSpan ℝ (((EuclideanSpace.equiv (Fin n) ℝ).symm) '' S) = _
    simpa [e, f] using (AffineSubspace.map_span f S).symm
  have hdir :
      ((affineSpan ℝ S).map f).direction = (affineSpan ℝ S).direction.map f.linear :=
    AffineSubspace.map_direction f (affineSpan ℝ S)
  rw [hspan]
  exact hdir.trans rfl

/-- The affine-span direction of a subset of `ℝ^n` and of its Euclidean realization have the
same dimension. -/
lemma finrank_direction_affineSpan_toEuclidean
    {n : ℕ}
    (S : Set (Fin n → ℝ)) :
    Module.finrank ℝ (affineSpan ℝ S).direction =
      Module.finrank ℝ (affineSpan ℝ S.toEuclidean).direction := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  rw [direction_affineSpan_toEuclidean]
  simpa [Submodule.toEuclidean, e] using
    (LinearEquiv.finrank_map_eq e (affineSpan ℝ S).direction).symm

/-- Helper for Exercise 3.12: a linear functional is constant on a nonempty set exactly when its
Euclidean realization is orthogonal to the direction of the affine span. -/
lemma constant_dotProduct_iff_mem_orthogonal_direction_affineSpan
    {n : ℕ}
    {S : Set (Fin n → ℝ)}
    (hS : Set.Nonempty S)
    (y : Fin n → ℝ) :
    (EuclideanSpace.equiv (Fin n) ℝ).symm y ∈ (affineSpan ℝ S).direction.toEuclideanᗮ ↔
      ∃ δ : ℝ, ∀ x ∈ S, y ⬝ᵥ x = δ := by
  rcases hS with ⟨x₀, hx₀⟩
  rw [direction_affineSpan,
    vectorSpan_eq_span_vsub_set_right ℝ hx₀,
    mem_toEuclidean_orthogonal_iff_dotProduct_eq_zero]
  constructor
  · intro hy
    refine ⟨y ⬝ᵥ x₀, ?_⟩
    intro x hx
    -- Every displacement from the base point lies in the spanned direction space.
    have hzero : y ⬝ᵥ (x - x₀) = 0 := hy (x - x₀) (Submodule.subset_span ⟨x, hx, rfl⟩)
    exact sub_eq_zero.mp <| by simpa [dotProduct_sub] using hzero
  · rintro ⟨δ, hδ⟩
    -- The constant-value hypothesis kills every generator of the direction space.
    let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ := (dotProductEquiv ℝ (Fin n)) y
    have hspan : Submodule.span ℝ ((fun x : Fin n → ℝ ↦ x - x₀) '' S) ≤ LinearMap.ker φ := by
      rw [Submodule.span_le]
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      change φ (x - x₀) = 0
      simp [φ, dotProduct_sub, hδ x hx, hδ x₀ hx₀]
    intro z hz
    exact by
      have hz' : z ∈ LinearMap.ker φ := hspan hz
      simpa [φ] using hz'

/-- Helper for Exercise 3.12: every balanced multiplier vector is constant on the primal
polyhedron. -/
lemma balanced_row_multiplier_constant_on_linear_system_polyhedron
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    {y : Fin n → ℝ}
    (hy : y ∈ balanced_row_multiplier_polyhedron A b) :
    ∃ δ : ℝ, ∀ x ∈ polyhedron_le_set A b, y ⬝ᵥ x = δ := by
  rcases hy with ⟨u, v, hu_nonneg, hv_nonpos, hu_row, hv_row, huv_eval⟩
  refine ⟨u ⬝ᵥ b, ?_⟩
  intro x hx
  have hAx : A *ᵥ x ≤ b := hx
  have hupper_aux : u ⬝ᵥ (A *ᵥ x) ≤ u ⬝ᵥ b :=
    dotProduct_le_dotProduct_of_nonneg_left hAx hu_nonneg
  have hneg_aux : (-v) ⬝ᵥ (A *ᵥ x) ≤ (-v) ⬝ᵥ b :=
    dotProduct_le_dotProduct_of_nonneg_left hAx (by simpa using neg_nonneg.mpr hv_nonpos)
  have hlower_aux : v ⬝ᵥ b ≤ v ⬝ᵥ (A *ᵥ x) := by
    have hneg' : -(v ⬝ᵥ (A *ᵥ x)) ≤ -(v ⬝ᵥ b) := by
      simpa [dotProduct] using hneg_aux
    linarith
  have hupper : y ⬝ᵥ x ≤ u ⬝ᵥ b := by
    -- The nonnegative certificate gives the upper bound.
    calc
      y ⬝ᵥ x = u ⬝ᵥ (A *ᵥ x) := by rw [hu_row, ← Matrix.dotProduct_mulVec]
      _ ≤ u ⬝ᵥ b := hupper_aux
  have hlower : u ⬝ᵥ b ≤ y ⬝ᵥ x := by
    -- The nonpositive certificate gives the matching lower bound.
    calc
      u ⬝ᵥ b = v ⬝ᵥ b := huv_eval
      _ ≤ v ⬝ᵥ (A *ᵥ x) := hlower_aux
      _ = y ⬝ᵥ x := by rw [hv_row, Matrix.dotProduct_mulVec]
  exact le_antisymm hupper hlower

/-- Helper for Exercise 3.12: a linear functional that is constant on the primal polyhedron
admits balanced multiplier certificates in both directions. -/
lemma mem_balanced_row_multiplier_polyhedron_of_constant_on_linear_system_polyhedron
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : Set.Nonempty (polyhedron_le_set A b))
    {y : Fin n → ℝ}
    (hy : ∃ δ : ℝ, ∀ x ∈ polyhedron_le_set A b, y ⬝ᵥ x = δ) :
    y ∈ balanced_row_multiplier_polyhedron A b := by
  rcases hP_nonempty with ⟨x₀, hx₀⟩
  have hP_nonempty : Set.Nonempty (polyhedron_le_set A b) := ⟨x₀, hx₀⟩
  rcases hy with ⟨δ, hδ⟩
  have hvalid_y : is_valid_inequality (polyhedron_le_set A b) y δ := by
    intro x hx
    exact le_of_eq (hδ x hx)
  have hvalid_neg_y : is_valid_inequality (polyhedron_le_set A b) (-y) (-δ) := by
    intro x hx
    simp [hδ x hx]
  rcases
      (valid_inequality_iff_exists_nonneg_row_multiplier A b y δ
        hP_nonempty).mp hvalid_y with
    ⟨u, hu_nonneg, hu_row, hu_eval_le⟩
  rcases
      (valid_inequality_iff_exists_nonneg_row_multiplier A b (-y) (-δ)
        hP_nonempty).mp hvalid_neg_y with
    ⟨w, hw_nonneg, hw_row, hw_eval_le⟩
  have hu_eval_eq : u ⬝ᵥ b = δ := by
    have hu_eval_ge : δ ≤ u ⬝ᵥ b := by
      calc
        δ = y ⬝ᵥ x₀ := (hδ x₀ hx₀).symm
        _ = u ⬝ᵥ (A *ᵥ x₀) := by rw [← hu_row, Matrix.dotProduct_mulVec]
        _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx₀ hu_nonneg
    exact le_antisymm hu_eval_le hu_eval_ge
  have hw_eval_eq : w ⬝ᵥ b = -δ := by
    have hw_eval_ge : -δ ≤ w ⬝ᵥ b := by
      calc
        -δ = (-y) ⬝ᵥ x₀ := by simp [hδ x₀ hx₀]
        _ = w ⬝ᵥ (A *ᵥ x₀) := by rw [← hw_row, Matrix.dotProduct_mulVec]
        _ ≤ w ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx₀ hw_nonneg
    exact le_antisymm hw_eval_le hw_eval_ge
  refine ⟨u, -w, hu_nonneg, ?_, hu_row.symm, ?_, ?_⟩
  · simpa using neg_nonpos.mpr hw_nonneg
  · rw [Matrix.neg_vecMul, hw_row, neg_neg]
  · calc
      u ⬝ᵥ b = δ := hu_eval_eq
      _ = (-w) ⬝ᵥ b := by simp [hw_eval_eq]

/-- Helper for Exercise 3.12: in the canonical Euclidean realization, the balanced multiplier
polyhedron is exactly the orthogonal complement of the direction of the affine hull of the primal
polyhedron. -/
lemma balanced_row_multiplier_polyhedron_eq_orthogonal_direction_affineSpan
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    (balanced_row_multiplier_polyhedron A b).toEuclidean =
      (((affineSpan ℝ (polyhedron_le_set A b)).direction.toEuclidean)ᗮ :
        Set (EuclideanSpace ℝ (Fin n))) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases balanced_row_multiplier_constant_on_linear_system_polyhedron A b hx with ⟨δ, hδ⟩
    -- Constantity on the polyhedron places `y` in the orthogonal complement.
    exact (constant_dotProduct_iff_mem_orthogonal_direction_affineSpan hP_nonempty x).2
      ⟨δ, hδ⟩
  · intro hy
    -- Orthogonality to the affine-span direction yields the balanced certificates.
    let x : Fin n → ℝ := (EuclideanSpace.equiv (Fin n) ℝ) y
    have hx :
        e x ∈ (affineSpan ℝ (polyhedron_le_set A b)).direction.toEuclideanᗮ := by
      simpa [e, x] using hy
    refine ⟨x, ?_, ?_⟩
    · exact mem_balanced_row_multiplier_polyhedron_of_constant_on_linear_system_polyhedron A b
        hP_nonempty <|
        (constant_dotProduct_iff_mem_orthogonal_direction_affineSpan hP_nonempty x).mp hx
    · simp [x]

/-- Exercise 3.12. If the polyhedron `P = {x : Fin n → ℝ | A *ᵥ x ≤ b}` is nonempty and
`Q = {y : Fin n → ℝ | ∃ u ≥ 0, ∃ v ≤ 0, y = u ᵥ* A = v ᵥ* A ∧ u ⬝ᵥ b = v ⬝ᵥ b}`, then the
dimensions of `P` and `Q` add up to `n`. -/
theorem linear_system_polyhedron_dim_add_balanced_row_multiplier_polyhedron_dim
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_nonempty : Set.Nonempty (polyhedron_le_set A b)) :
    Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction +
      Module.finrank ℝ (affineSpan ℝ (balanced_row_multiplier_polyhedron A b)).direction =
        n := by
  let L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    (affineSpan ℝ (polyhedron_le_set A b)).direction.toEuclidean
  have hQ :
      (balanced_row_multiplier_polyhedron A b).toEuclidean =
        (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) := by
    -- First identify the balanced multiplier set with the orthogonal complement.
    simpa [L] using
      balanced_row_multiplier_polyhedron_eq_orthogonal_direction_affineSpan A b hP_nonempty
  have hQdir :
      (affineSpan ℝ (balanced_row_multiplier_polyhedron A b).toEuclidean).direction = Lᗮ := by
    rw [hQ]
    rw [show affineSpan ℝ (Lᗮ : Set (EuclideanSpace ℝ (Fin n))) = (Lᗮ).toAffineSubspace from
      AffineSubspace.affineSpan_coe (Lᗮ).toAffineSubspace]
    exact Submodule.toAffineSubspace_direction (Lᗮ)
  have hfinrank :
      Module.finrank ℝ L + Module.finrank ℝ Lᗮ = n := by
    simpa [L, finrank_euclideanSpace_fin] using L.finrank_add_finrank_orthogonal
  calc
    Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b)).direction +
        Module.finrank ℝ (affineSpan ℝ (balanced_row_multiplier_polyhedron A b)).direction
      = Module.finrank ℝ (affineSpan ℝ (polyhedron_le_set A b).toEuclidean).direction +
          Module.finrank ℝ
            (affineSpan ℝ (balanced_row_multiplier_polyhedron A b).toEuclidean).direction := by
          rw [← finrank_direction_affineSpan_toEuclidean (polyhedron_le_set A b),
            ← finrank_direction_affineSpan_toEuclidean (balanced_row_multiplier_polyhedron A b)]
    _ = Module.finrank ℝ L + Module.finrank ℝ Lᗮ := by
      rw [direction_affineSpan_toEuclidean, hQdir]
    _ = n := by
      exact hfinrank

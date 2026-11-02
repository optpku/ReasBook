import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_definition_3_16_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_remark_3_16_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_16.ch3_sec3_16_theorem_3_49
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1

open scoped Matrix Pointwise Polar

-- Declarations for this item will be appended below by the statement pipeline.

section Corollary350

variable {n : ℕ}
variable (P : Set (Fin n → ℝ))

local notation "Pe" => Set.toEuclidean P
local notation "linP" => Submodule.toEuclidean (linealitySubmodule P)

/-- Helper for Corollary 3.50: the canonical Euclidean realization of a subset of `ℝ^n` agrees
with the `toLp 2` image used in Theorem 3.49. -/
lemma toEuclidean_eq_toLpImage :
    Pe = (WithLp.toLp 2 '' P) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    -- The Euclidean realization map is the `toLp 2` embedding on `ℝ^n`.
    refine ⟨x, hx, ?_⟩
    simpa using congrFun (EuclideanSpace.coe_measurableEquiv_symm (Fin n)) x
  · rintro ⟨x, hx, rfl⟩
    -- The same identification works in the reverse direction.
    refine ⟨x, hx, ?_⟩
    simpa using (congrFun (EuclideanSpace.coe_measurableEquiv_symm (Fin n)) x).symm

/-- Helper for Corollary 3.50: any polyhedron containing `0` admits a mixed `1/0` right-hand-side
presentation after duplicating the row set into normalized and homogeneous blocks. -/
lemma exists_mixedRhsEuclideanPresentation
    (hP : is_polyhedron P)
    (h0 : (0 : Fin n → ℝ) ∈ P) :
    ∃ m : ℕ, ∃ A : Matrix (Fin m) (Fin n) ℝ, ∃ k : ℕ,
      Pe = (WithLp.toLp 2 '' polyhedron_le_set A (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0)) := by
  rcases is_polyhedron_iff.mp hP with ⟨m, A, b, rfl⟩
  have hb_nonneg : ∀ i : Fin m, 0 ≤ b i := by
    intro i
    have h0' : (0 : Fin n → ℝ) ∈ polyhedron_le_set A b := h0
    have hi : (A *ᵥ (0 : Fin n → ℝ)) i ≤ b i := h0' i
    simpa [Matrix.mulVec] using hi
  let earlyRows : Matrix (Fin m) (Fin n) ℝ :=
    fun i ↦ if hb : b i = 0 then 0 else (b i)⁻¹ • A i
  let lateRows : Matrix (Fin m) (Fin n) ℝ :=
    fun i ↦ if b i = 0 then A i else 0
  let mixedRows : Matrix (Fin (m + m)) (Fin n) ℝ :=
    Fin.append earlyRows lateRows
  refine ⟨m + m, mixedRows, m, ?_⟩
  rw [toEuclidean_eq_toLpImage]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    -- Original inequalities imply both the normalized and homogeneous blocks.
    intro i
    by_cases hi : i.1 < m
    · let j : Fin m := ⟨i.1, hi⟩
      have hij : Fin.castAdd m j = i := by
        ext
        simp [j]
      have hrow : mixedRows (Fin.castAdd m j) = earlyRows j := by
        simpa [mixedRows] using (Fin.append_left earlyRows lateRows j)
      by_cases hb : b j = 0
      · rw [← hij]
        have heval : (mixedRows *ᵥ x) (Fin.castAdd m j) = 0 := by
          rw [Matrix.mulVec, hrow]
          simp [earlyRows, hb]
        have htrivial : (0 : ℝ) ≤ 1 := by norm_num
        simpa [heval] using htrivial
      · have hb_pos : 0 < b j := lt_of_le_of_ne (hb_nonneg j) (Ne.symm hb)
        have hxj : (A *ᵥ x) j ≤ b j := hx j
        have hmul :
            (b j)⁻¹ * ((A *ᵥ x) j) ≤ (b j)⁻¹ * b j :=
          mul_le_mul_of_nonneg_left hxj (inv_nonneg.mpr (hb_nonneg j))
        have hscaled : (b j)⁻¹ * ((A *ᵥ x) j) ≤ 1 := by
          simpa [hb_pos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul
        rw [← hij]
        have heval : (mixedRows *ᵥ x) (Fin.castAdd m j) = (b j)⁻¹ * ((A *ᵥ x) j) := by
          rw [Matrix.mulVec, hrow, Matrix.mulVec]
          calc
            (earlyRows j) ⬝ᵥ x = (((b j)⁻¹ : ℝ) • A j) ⬝ᵥ x := by simp [earlyRows, hb]
            _ = (b j)⁻¹ * (A j ⬝ᵥ x) := by
              simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
                (smul_dotProduct ((b j)⁻¹) (A j) x)
            _ = (b j)⁻¹ * ((A *ᵥ x) j) := by rw [Matrix.mulVec]
        rw [heval]
        simpa using hscaled
    · have hi_ge : m ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin m := ⟨i.1 - m, by omega⟩
      have hij : Fin.natAdd m j = i := by
        ext
        simp [j, hi_ge, Nat.add_sub_of_le hi_ge]
      have hrow : mixedRows (Fin.natAdd m j) = lateRows j := by
        simpa [mixedRows] using (Fin.append_right earlyRows lateRows j)
      by_cases hb : b j = 0
      · have hxj : (A *ᵥ x) j ≤ 0 := by
          simpa [hb] using hx j
        rw [← hij]
        have heval : (mixedRows *ᵥ x) (Fin.natAdd m j) = (A *ᵥ x) j := by
          rw [Matrix.mulVec, hrow, Matrix.mulVec]
          simp [lateRows, hb]
        rw [heval]
        simpa using hxj
      · rw [← hij]
        have heval : (mixedRows *ᵥ x) (Fin.natAdd m j) = 0 := by
          rw [Matrix.mulVec, hrow]
          simp [lateRows, hb]
        have hrhs : (fun j : Fin (m + m) ↦ if j.1 < m then (1 : ℝ) else 0) (Fin.natAdd m j) = 0 := by
          simp
        rw [hrhs]
        exact le_of_eq heval
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    -- The doubled-row system recovers the original inequalities row by row.
    intro i
    by_cases hb : b i = 0
    · have hlate : (A *ᵥ x) i ≤ 0 := by
        have hrow : mixedRows (Fin.natAdd m i) = lateRows i := by
          simpa [mixedRows] using (Fin.append_right earlyRows lateRows i)
        have hlate' := hx (Fin.natAdd m i)
        have heval : (mixedRows *ᵥ x) (Fin.natAdd m i) = (A *ᵥ x) i := by
          rw [Matrix.mulVec, hrow, Matrix.mulVec]
          simp [lateRows, hb]
        have hrhs : (fun j : Fin (m + m) ↦ if j.1 < m then (1 : ℝ) else 0) (Fin.natAdd m i) = 0 := by
          simp
        exact (by rwa [heval, hrhs] at hlate')
      simpa [hb] using hlate
    · have hb_pos : 0 < b i := lt_of_le_of_ne (hb_nonneg i) (Ne.symm hb)
      have hearly : (b i)⁻¹ * ((A *ᵥ x) i) ≤ 1 := by
        have hrow : mixedRows (Fin.castAdd m i) = earlyRows i := by
          simpa [mixedRows] using (Fin.append_left earlyRows lateRows i)
        have hearly' := hx (Fin.castAdd m i)
        have heval : (mixedRows *ᵥ x) (Fin.castAdd m i) = (b i)⁻¹ * ((A *ᵥ x) i) := by
          rw [Matrix.mulVec, hrow, Matrix.mulVec]
          calc
            (earlyRows i) ⬝ᵥ x = (((b i)⁻¹ : ℝ) • A i) ⬝ᵥ x := by simp [earlyRows, hb]
            _ = (b i)⁻¹ * (A i ⬝ᵥ x) := by
              simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using
                (smul_dotProduct ((b i)⁻¹) (A i) x)
            _ = (b i)⁻¹ * ((A *ᵥ x) i) := by rw [Matrix.mulVec]
        have hrhs : (fun j : Fin (m + m) ↦ if j.1 < m then (1 : ℝ) else 0) (Fin.castAdd m i) = 1 := by
          simp
        exact (by rwa [heval, hrhs] at hearly')
      have hmul :
          (b i) * ((b i)⁻¹ * ((A *ᵥ x) i)) ≤ (b i) * 1 :=
        mul_le_mul_of_nonneg_left hearly hb_pos.le
      simpa [hb_pos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Helper for Corollary 3.50: the lineality submodule commutes with the canonical Euclidean
realization of `ℝ^n`. -/
lemma toEuclidean_linealitySubmodule_eq :
    linealitySubmodule Pe = linP := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  ext x
  have hlineality :
      x ∈ linealitySubmodule Pe ↔ e.symm x ∈ linealitySubmodule P := by
    rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff, mem_linealitySubmodule_iff,
      mem_linealitySpace_iff]
    constructor
    · intro hx y hy a
      have hy' : e y ∈ Pe := ⟨y, hy, rfl⟩
      have hshift : e y + a • x ∈ Pe := hx hy' a
      rcases hshift with ⟨z, hz, hzEq⟩
      have hzRaw : z = y + a • e.symm x := by
        apply e.injective
        simpa [e.map_add, e.map_smul] using hzEq
      exact hzRaw ▸ hz
    · intro hx y hy a
      rcases hy with ⟨z, hz, rfl⟩
      refine ⟨z + a • e.symm x, hx hz a, ?_⟩
      calc
        e (z + a • e.symm x) = e z + e (a • e.symm x) := by rw [e.map_add]
        _ = e z + a • x := by simp [e.map_smul]
  have hmap :
      x ∈ linP ↔ e.symm x ∈ linealitySubmodule P := by
    simpa [Submodule.toEuclidean, e] using
      (Submodule.mem_map_equiv (linealitySubmodule P) (x := x) (e := e))
  exact hlineality.trans hmap.symm

/-- Helper for Corollary 3.50: when `0 ∈ S`, orthogonality to the direction of `affineSpan ℝ S`
is equivalent to vanishing on every point of `S`. -/
lemma mem_orthogonal_direction_affineSpan_iff_inner_eq_zero
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (h0S : (0 : EuclideanSpace ℝ (Fin n)) ∈ S)
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ (affineSpan ℝ S).directionᗮ ↔ ∀ y ∈ S, inner ℝ y x = 0 := by
  have hdir : (affineSpan ℝ S).direction = Submodule.span ℝ S := by
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0S]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨y, hy, by simp⟩
  rw [hdir, Submodule.mem_orthogonal]
  constructor
  · intro hx y hy
    exact hx y (Submodule.subset_span hy)
  · intro hx y hy
    -- Span induction reduces the orthogonality check to the generators in `S`.
    refine Submodule.span_induction (fun z hz ↦ hx z hz) ?_ ?_ ?_ hy
    · simp
    · intro z w _ _ hz hw
      simp [inner_add_left, hz, hw]
    · intro a z _ hz
      simp [inner_smul_left, hz]

/-- Helper for Corollary 3.50: a set with `0 ∈ S` and `S** = S` has lineality submodule equal to
the orthogonal complement of the direction of the affine span of its polar. -/
lemma linealitySubmodule_eq_orthogonal_direction_affineSpan_polar
    {S : Set (EuclideanSpace ℝ (Fin n))}
    (h0S : (0 : EuclideanSpace ℝ (Fin n)) ∈ S)
    (hSS : S** = S) :
    linealitySubmodule S = (affineSpan ℝ (S*)).directionᗮ := by
  ext x
  rw [mem_linealitySubmodule_iff, mem_linealitySpace_iff,
    mem_orthogonal_direction_affineSpan_iff_inner_eq_zero (S := S*) (Set.zero_mem_polar S) x]
  constructor
  · intro hx y hy
    -- Every scalar multiple of `x` stays in `S`, so a nonzero pairing would violate polarity.
    by_contra hxy
    let a : ℝ := 2 / inner ℝ y x
    have hax : a • x ∈ S := by
      simpa [a] using hx h0S a
    have hpolar : inner ℝ y (a • x) ≤ 1 := (Set.mem_polar_iff S y).1 hy _ hax
    have htwo : inner ℝ y (a • x) = 2 := by
      calc
        inner ℝ y (a • x) = a * inner ℝ y x := by rw [inner_smul_right]
        _ = 2 := by
          dsimp [a]
          field_simp [hxy]
    linarith
  · intro hx z hz a
    -- Route correction: use the bipolar identity directly on `S**` instead of unfolding lineality
    -- through recession cones.
    have hzax : z + a • x ∈ S** := by
      rw [Set.mem_polar_iff]
      intro y hy
      have hyz : inner ℝ z y ≤ 1 := by
        simpa [real_inner_comm] using (Set.mem_polar_iff S y).1 hy z hz
      have hyx : inner ℝ x y = 0 := by
        simpa [real_inner_comm] using hx y hy
      calc
        inner ℝ (z + a • x) y = inner ℝ z y + a * inner ℝ x y := by
          simp [inner_add_left, inner_smul_left]
        _ = inner ℝ z y := by rw [hyx, mul_zero, add_zero]
        _ ≤ 1 := hyz
    simpa [hSS] using hzax

/-- Corollary 3.50 (1). Let `P ⊆ ℝ^n` be a polyhedron containing the origin. Then taking the
polar twice recovers its canonical Euclidean realization. -/
theorem polyhedron_polar_polar_eq_self
    (hP : is_polyhedron P)
    (h0 : (0 : Fin n → ℝ) ∈ P) :
    Pe** = Pe := by
  rcases exists_mixedRhsEuclideanPresentation (P := P) hP h0 with ⟨m, A, k, hPe⟩
  -- Normalize `P` to the mixed `1/0` presentation from Theorem 3.49.
  rw [hPe]
  calc
    ((WithLp.toLp 2 ''
        polyhedron_le_set A (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0))*)*
        =
        (convexHull ℝ ({0} ∪ Set.range (fun i : {j : Fin m // j.1 < k} ↦ WithLp.toLp 2 (A i.1))) +
          (WithLp.toLp 2 '' cone (Set.range (fun i : {j : Fin m // k ≤ j.1} ↦ A i.1))))* := by
          rw [polar_mixed_rhs_polyhedron_eq_convexHull_add_cone A k]
    _ = (WithLp.toLp 2 ''
        polyhedron_le_set A (fun i : Fin m ↦ if i.1 < k then (1 : ℝ) else 0)) := by
          exact polar_convexHull_add_cone_eq_mixed_rhs_polyhedron A k

/-- Corollary 3.50 (2). Let `P ⊆ ℝ^n` be a polyhedron containing the origin. Then its polar is
bounded if and only if the origin lies in the interior of its canonical Euclidean realization. -/
theorem polyhedron_bounded_polar_iff_zero_mem_interior
    (hP : is_polyhedron P)
    (h0 : (0 : Fin n → ℝ) ∈ P) :
    Bornology.IsBounded (Pe*) ↔ (0 : EuclideanSpace ℝ (Fin n)) ∈ interior Pe := by
  constructor
  · intro hbounded
    have hpp : Pe** = Pe := polyhedron_polar_polar_eq_self (P := P) hP h0
    rcases Bornology.IsBounded.subset_ball hbounded (0 : EuclideanSpace ℝ (Fin n)) with ⟨R, hR⟩
    have hRpos : 0 < R := by
      have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 R := hR (Set.zero_mem_polar Pe)
      simpa [mem_ball_zero_iff] using hzero
    have hball : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R⁻¹ ⊆ Pe := by
      intro x hx
      have hxpp : x ∈ Pe** := by
        rw [Set.mem_polar_iff]
        intro y hy
        have hyR : ‖y‖ < R := by
          have : y ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R := hR hy
          simpa [mem_ball_zero_iff] using this
        have hxR : ‖x‖ < R⁻¹ := by simpa [mem_ball_zero_iff] using hx
        have hprod : ‖y‖ * ‖x‖ < 1 := by
          have hlt : ‖y‖ * ‖x‖ < R * R⁻¹ :=
            mul_lt_mul_of_nonneg_of_pos hyR hxR.le (norm_nonneg _) (inv_pos.mpr hRpos)
          simpa [hRpos.ne', mul_inv_cancel₀] using hlt
        have hinner : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
        have hswap : ‖x‖ * ‖y‖ = ‖y‖ * ‖x‖ := by ring
        rw [hswap] at hinner
        exact le_trans hinner hprod.le
      simpa [hpp] using hxpp
    -- A positive-radius ball inside `Pe` places `0` in the interior.
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    exact ⟨R⁻¹, inv_pos.mpr hRpos, hball⟩
  · intro hInterior
    rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hInterior) with ⟨ε, hεpos, hε⟩
    refine (Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (Fin n))).2 ?_
    refine ⟨2 / ε, ?_⟩
    intro y hy
    by_cases hy0 : y = 0
    · have hnonneg : 0 ≤ 2 / ε := by positivity
      simpa [hy0, mem_closedBall_zero_iff] using hnonneg
    · have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy0
      let t : ℝ := ε / 2 / ‖y‖
      have ht_pos : 0 < t := by
        dsimp [t]
        positivity
      have ht_mem : t • y ∈ Pe := by
        have hnorm : ‖t • y‖ = ε / 2 := by
          calc
            ‖t • y‖ = |t| * ‖y‖ := by simpa [Real.norm_eq_abs] using norm_smul t y
            _ = t * ‖y‖ := by rw [abs_of_pos ht_pos]
            _ = ε / 2 := by
              dsimp [t]
              field_simp [hy_norm_pos.ne']
        have hhalf : ε / 2 < ε := by linarith
        apply hε
        rw [mem_ball_zero_iff, hnorm]
        exact hhalf
      have hpolar : inner ℝ y (t • y) ≤ 1 := (Set.mem_polar_iff Pe y).1 hy _ ht_mem
      have htnorm : t * ‖y‖ = ε / 2 := by
        dsimp [t]
        field_simp [hy_norm_pos.ne']
      have hscaled : inner ℝ y (t • y) = (ε / 2) * ‖y‖ := by
        calc
          inner ℝ y (t • y) = t * (‖y‖ * ‖y‖) := by rw [real_inner_smul_self_right]
          _ = (t * ‖y‖) * ‖y‖ := by ring
          _ = (ε / 2) * ‖y‖ := by rw [htnorm]
      have hy_bound : ‖y‖ ≤ 2 / ε := by
        rw [hscaled] at hpolar
        have hmul : ε * ‖y‖ ≤ 2 := by nlinarith
        exact (le_div_iff₀ hεpos).2 <| by simpa [mul_comm] using hmul
      simpa [mem_closedBall_zero_iff] using hy_bound

/-- Corollary 3.50 (3). Let `P ⊆ ℝ^n` be a polyhedron containing the origin. Then the affine hull
of its polar is the affine subspace through the origin whose direction is the orthogonal complement
of its canonical lineality submodule in the Euclidean realization. -/
theorem polyhedron_affineSpan_direction_polar_eq_orthogonal_linealitySpace
    (hP : is_polyhedron P)
    (h0 : (0 : Fin n → ℝ) ∈ P) :
    affineSpan ℝ (Pe*) = (linPᗮ).toAffineSubspace := by
  have hpp : Pe** = Pe := polyhedron_polar_polar_eq_self (P := P) hP h0
  have hlineality :
      linealitySubmodule Pe = (affineSpan ℝ (Pe*)).directionᗮ :=
    linealitySubmodule_eq_orthogonal_direction_affineSpan_polar (S := Pe) (by
      exact ⟨0, h0, by simp⟩) hpp
  have hlin : linealitySubmodule Pe = linP := toEuclidean_linealitySubmodule_eq (P := P)
  have hdir : (affineSpan ℝ (Pe*)).direction = linPᗮ := by
    have horth :
        linPᗮ = ((affineSpan ℝ (Pe*)).directionᗮ)ᗮ := by
      simpa [hlin] using congrArg (fun L : Submodule ℝ (EuclideanSpace ℝ (Fin n)) ↦ Lᗮ) hlineality
    calc
      (affineSpan ℝ (Pe*)).direction = ((affineSpan ℝ (Pe*)).directionᗮ)ᗮ := by
        symm
        exact Submodule.orthogonal_orthogonal _
      _ = linPᗮ := by simpa using horth.symm
  have h0polar : (0 : EuclideanSpace ℝ (Fin n)) ∈ affineSpan ℝ (Pe*) :=
    (subset_affineSpan ℝ (Pe*)) (Set.zero_mem_polar Pe)
  have h0orth : (0 : EuclideanSpace ℝ (Fin n)) ∈ (linPᗮ).toAffineSubspace := by
    simpa [Submodule.mem_toAffineSubspace]
  -- The two affine subspaces have the same direction and both contain the origin.
  have hdirAff :
      (affineSpan ℝ (Pe*)).direction = (linPᗮ).toAffineSubspace.direction := by
    simpa [Submodule.toAffineSubspace_direction] using hdir
  exact AffineSubspace.ext_of_direction_eq hdirAff ⟨0, h0polar, h0orth⟩

/-- Companion consequence of Corollary 3.50 (3): the dimension of the affine hull of the polar is
`n - dim(lin(P))`, expressed through the direction of that affine hull and the canonical lineality
submodule. -/
theorem polyhedron_finrank_affineSpan_direction_polar_eq_sub_finrank_linealitySpace
    (hP : is_polyhedron P)
    (h0 : (0 : Fin n → ℝ) ∈ P) :
    Module.finrank ℝ (affineSpan ℝ (Pe*)).direction =
      n - Module.finrank ℝ (linealitySubmodule P) := by
  let e : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearEquiv
  have hdir :
      (affineSpan ℝ (Pe*)).direction = linPᗮ := by
    simpa [Submodule.toAffineSubspace_direction] using
      congrArg AffineSubspace.direction
        (polyhedron_affineSpan_direction_polar_eq_orthogonal_linealitySpace (P := P) hP h0)
  have hlinfin :
      Module.finrank ℝ linP = Module.finrank ℝ (linealitySubmodule P) := by
    simpa [Submodule.toEuclidean, e] using
      (LinearEquiv.finrank_map_eq e (linealitySubmodule P))
  have hsum : Module.finrank ℝ linP + Module.finrank ℝ linPᗮ = n :=
    finrank_add_finrank_orthogonal_eq_fin linP
  have hsub : Module.finrank ℝ linPᗮ = n - Module.finrank ℝ linP := by
    omega
  -- Rewrite the Euclidean-side dimension identity back in terms of `linealitySubmodule P`.
  rw [hdir, hsub, hlinfin]

end Corollary350

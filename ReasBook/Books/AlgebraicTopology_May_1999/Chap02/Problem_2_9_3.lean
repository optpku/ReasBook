/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval ContinuousMap TopCat

noncomputable section

local notation "V[" n "]" => EuclideanSpace ℝ (Fin (n + 1))

/-- The subspace of `S^n × S^n` consisting of pairs of non-antipodal points. -/
abbrev nonantipodal_pair_space (n : ℕ) :=
  {pq : 𝕊 n × 𝕊 n | pq.1.down ≠ -pq.2.down}

-- Proof sketch: both coordinates are equal to `p`, so antipodality would force `p = -p`; taking
-- norms contradicts the defining equation `‖p‖ = 1` for points on the unit sphere.
/-- The diagonal pair `(p, p)` is non-antipodal. -/
theorem sphere_diagonal_pair_nonantipodal
    (n : ℕ) (p : 𝕊 n) : p.down ≠ -p.down := by
  simpa using ne_neg_of_mem_unit_sphere ℝ p.down

/-- The diagonal map from `S^n` to the space of non-antipodal pairs in `S^n × S^n`. -/
def sphere_diagonal_map (n : ℕ) : C(𝕊 n, nonantipodal_pair_space n) where
  toFun p := ⟨(p, p), sphere_diagonal_pair_nonantipodal n p⟩
  continuous_toFun := (continuous_id.prodMk continuous_id).subtype_mk
    (fun p ↦ sphere_diagonal_pair_nonantipodal n p)

/-- Evaluating the diagonal map returns the diagonal pair. -/
@[simp] theorem sphere_diagonal_map_apply (n : ℕ) (p : 𝕊 n) :
    sphere_diagonal_map n p =
      ⟨(p, p), sphere_diagonal_pair_nonantipodal n p⟩ :=
  rfl

/-- Helper for Problem 2.9.3: the normalization of a nonzero vector lies on the unit sphere. -/
lemma normalize_mem_unit_sphere {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {v : V} (hv : v ≠ 0) : NormedSpace.normalize v ∈ Metric.sphere (0 : V) 1 := by
  -- Turn the goal into the norm-one characterization of the unit sphere.
  simpa [mem_sphere_zero_iff_norm] using NormedSpace.norm_normalize hv

/-- Helper for Problem 2.9.3: package a nonzero vector as the corresponding point on the unit
sphere obtained by normalization. -/
def normalize_to_sphere {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : V) (hv : v ≠ 0) : Metric.sphere (0 : V) 1 :=
  ⟨NormedSpace.normalize v, normalize_mem_unit_sphere hv⟩

/-- Helper for Problem 2.9.3: the normalized nonzero-vector construction is continuous. -/
lemma normalize_to_sphere_map_continuous {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : C(X, V)) (hf : ∀ x, f x ≠ 0) :
    Continuous fun x ↦ normalize_to_sphere (f x) (hf x) := by
  -- Continuity comes from the explicit formula `normalize x = ‖x‖⁻¹ • x`.
  apply Continuous.subtype_mk
  simpa [normalize_to_sphere, NormedSpace.normalize] using
    ((continuous_norm.comp f.continuous).inv₀ fun x ↦ norm_ne_zero_iff.mpr (hf x)).smul
      f.continuous

/-- Helper for Problem 2.9.3: normalize a continuous nonvanishing vector field into the unit
sphere. -/
def normalize_to_sphere_map {X V : Type*} [TopologicalSpace X]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (f : C(X, V)) (hf : ∀ x, f x ≠ 0) :
    C(X, Metric.sphere (0 : V) 1) where
  toFun x := normalize_to_sphere (f x) (hf x)
  continuous_toFun := normalize_to_sphere_map_continuous f hf

/-- Helper for Problem 2.9.3: forgetting the non-antipodal condition gives a continuous map into
`S^n × S^n`. -/
def nonantipodal_pair_val_map (n : ℕ) : C(nonantipodal_pair_space n, 𝕊 n × 𝕊 n) :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- Helper for Problem 2.9.3: projection to the first sphere coordinate. -/
def sphere_first_projection (n : ℕ) : C(nonantipodal_pair_space n, 𝕊 n) :=
  ContinuousMap.fst.comp (nonantipodal_pair_val_map n)

/-- Helper for Problem 2.9.3: projection to the second sphere coordinate. -/
def sphere_second_projection (n : ℕ) : C(nonantipodal_pair_space n, 𝕊 n) :=
  ContinuousMap.snd.comp (nonantipodal_pair_val_map n)

/-- Helper for Problem 2.9.3: the ambient straight-line segment from `p` to `q`. -/
def sphere_segment_vector (n : ℕ) (t : ℝ) (p q : 𝕊 n) : V[n] :=
  (1 - t) • ((p.down : Metric.sphere (0 : V[n]) 1) : V[n]) +
    t • ((q.down : Metric.sphere (0 : V[n]) 1) : V[n])

/-- Helper for Problem 2.9.3: a non-antipodal pair has no zero convex combination on the segment
joining its endpoints on the sphere. -/
lemma sphere_segment_vector_ne_zero (n : ℕ) {p q : 𝕊 n} (h : p.down ≠ -q.down)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphere_segment_vector n t p q ≠ 0 := by
  let pv : V[n] := (p.down : Metric.sphere (0 : V[n]) 1)
  let qv : V[n] := (q.down : Metric.sphere (0 : V[n]) 1)
  intro hw
  have hw' : t • qv + (1 - t) • pv = 0 := by
    simpa [sphere_segment_vector, pv, qv, add_comm] using hw
  have hEq : t • qv = -((1 - t) • pv) := eq_neg_of_add_eq_zero_left hw'
  -- Compare norms to force the convex coefficients to coincide.
  have hnorm' : |t| = |1 - t| := by
    have := congrArg norm hEq
    simpa [pv, qv, norm_smul] using this
  have hnorm : t = 1 - t := by
    rwa [abs_of_nonneg ht0, abs_of_nonneg (sub_nonneg.mpr ht1)] at hnorm'
  have hnorm2 : 1 - t = t := hnorm.symm
  have ht_pos : 0 < t := by
    by_contra ht
    have ht' : t = 0 := by linarith
    linarith [hnorm]
  have hqv : qv = -pv := by
    apply (smul_right_injective (M := V[n]) (show t ≠ 0 by linarith))
    calc
      t • qv = -((1 - t) • pv) := hEq
      _ = t • (-pv) := by rw [hnorm2, smul_neg]
  have hpv : pv = -qv := by
    simpa [eq_comm] using congrArg Neg.neg hqv
  have hcontra : p.down = -q.down := by
    apply Subtype.ext
    simpa [pv, qv] using hpv
  exact h hcontra

/-- Helper for Problem 2.9.3: the normalized point on the straight-line segment from `p` to `q`. -/
def sphere_segment_point (n : ℕ) (t : ℝ) (p q : 𝕊 n) (h : p.down ≠ -q.down)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Metric.sphere (0 : V[n]) 1 :=
  normalize_to_sphere (sphere_segment_vector n t p q) (sphere_segment_vector_ne_zero n h ht0 ht1)

/-- Helper for Problem 2.9.3: at time `0`, the normalized segment returns the first endpoint. -/
@[simp] lemma sphere_segment_point_zero (n : ℕ) (p q : 𝕊 n) (h : p.down ≠ -q.down) :
    sphere_segment_point n 0 p q h le_rfl zero_le_one = p.down := by
  -- The segment vector is exactly `p`, so normalization fixes it.
  apply Subtype.ext
  simp [sphere_segment_point, sphere_segment_vector, normalize_to_sphere,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Problem 2.9.3: at time `1`, the normalized segment returns the second endpoint. -/
@[simp] lemma sphere_segment_point_one (n : ℕ) (p q : 𝕊 n) (h : p.down ≠ -q.down) :
    sphere_segment_point n 1 p q h zero_le_one le_rfl = q.down := by
  -- The segment vector is exactly `q`, so normalization fixes it.
  apply Subtype.ext
  simp [sphere_segment_point, sphere_segment_vector, normalize_to_sphere,
    NormedSpace.normalize_eq_self_of_norm_eq_one]

/-- Helper for Problem 2.9.3: the normalized segment never lands at the antipode of the initial
point. -/
lemma sphere_segment_point_ne_neg_left (n : ℕ) {p q : 𝕊 n} (h : p.down ≠ -q.down)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    sphere_segment_point n t p q h ht0 ht1 ≠ -p.down := by
  let pv : V[n] := (p.down : Metric.sphere (0 : V[n]) 1)
  let qv : V[n] := (q.down : Metric.sphere (0 : V[n]) 1)
  let w : V[n] := sphere_segment_vector n t p q
  intro hneg
  have hvec : NormedSpace.normalize w = -(pv : V[n]) := by
    exact congrArg Subtype.val hneg
  have hw_eq : w = -(‖w‖ • pv) := by
    -- Rewrite the segment vector using the assumed antipodality of its normalization.
    calc
      w = ‖w‖ • NormedSpace.normalize w := by simp [w]
      _ = -(‖w‖ • pv) := by rw [hvec, smul_neg]
  have hsum : t • qv + ((1 - t) + ‖w‖) • pv = 0 := by
    have hsum0 : w + ‖w‖ • pv = 0 := eq_neg_iff_add_eq_zero.mp hw_eq
    simpa [sphere_segment_vector, pv, qv, w, add_assoc, add_left_comm, add_comm, add_smul] using
      hsum0
  have hw_eq' : t • qv = -(((1 - t) + ‖w‖) • pv) := eq_neg_of_add_eq_zero_left hsum
  -- Norms now identify the positive coefficient of `pv` with the coefficient `t` of `qv`.
  have hnorm : t = (1 - t) + ‖w‖ := by
    have := congrArg norm hw_eq'
    simpa [pv, qv, norm_smul, abs_of_nonneg ht0,
      abs_of_nonneg (add_nonneg (sub_nonneg.mpr ht1) (norm_nonneg _))] using this
  have hnorm2 : (1 - t) + ‖w‖ = t := hnorm.symm
  have hqv : qv = -pv := by
    apply (smul_right_injective (M := V[n]) (show t ≠ 0 by
      intro ht
      linarith [norm_nonneg w]))
    calc
      t • qv = -(((1 - t) + ‖w‖) • pv) := hw_eq'
      _ = t • (-pv) := by rw [hnorm2, smul_neg]
  have hpv : pv = -qv := by
    simpa [eq_comm] using congrArg Neg.neg hqv
  have hcontra : p.down = -q.down := by
    apply Subtype.ext
    simpa [pv, qv] using hpv
  exact h hcontra

/-- Helper for Problem 2.9.3: the ambient segment vector varies continuously with time and the
non-antipodal pair. -/
lemma sphere_segment_vector_map_continuous (n : ℕ) :
    Continuous fun x : unitInterval × nonantipodal_pair_space n =>
      sphere_segment_vector n x.1 x.2.1.1 x.2.1.2 := by
  -- This is a direct continuity check for the explicit affine formula.
  simpa [sphere_segment_vector] using
    (show Continuous fun x : unitInterval × nonantipodal_pair_space n =>
      (1 - (x.1 : ℝ)) • (((x.2.1.1).down : Metric.sphere (0 : V[n]) 1) : V[n]) +
        (x.1 : ℝ) • (((x.2.1.2).down : Metric.sphere (0 : V[n]) 1) : V[n]) by
      fun_prop)

/-- Helper for Problem 2.9.3: the ambient segment vector as a continuous map. -/
def sphere_segment_vector_map (n : ℕ) : C(unitInterval × nonantipodal_pair_space n, V[n]) where
  toFun x := sphere_segment_vector n x.1 x.2.1.1 x.2.1.2
  continuous_toFun := sphere_segment_vector_map_continuous n

/-- Helper for Problem 2.9.3: the normalized segment as a continuous map into the raw sphere. -/
def sphere_segment_raw_map (n : ℕ) :
    C(unitInterval × nonantipodal_pair_space n, Metric.sphere (0 : V[n]) 1) :=
  normalize_to_sphere_map (sphere_segment_vector_map n)
    (fun x ↦ sphere_segment_vector_ne_zero n x.2.2 x.1.2.1 x.1.2.2)

/-- Helper for Problem 2.9.3: the normalized segment as a continuous map into `S^n`. -/
def sphere_segment_map (n : ℕ) : C(unitInterval × nonantipodal_pair_space n, 𝕊 n) :=
  ⟨ULift.up ∘ sphere_segment_raw_map n, continuous_uliftUp.comp (sphere_segment_raw_map n).continuous⟩

/-- Helper for Problem 2.9.3: the segment homotopy starts at the first projection. -/
lemma sphere_segment_map_zero (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_segment_map n (0, pq) = sphere_first_projection n pq := by
  -- Unwrap the `ULift` and use the `t = 0` endpoint computation.
  apply ULift.ext
  change sphere_segment_point n 0 pq.1.1 pq.1.2 pq.2 le_rfl zero_le_one = pq.1.1.down
  exact sphere_segment_point_zero n pq.1.1 pq.1.2 pq.2

/-- Helper for Problem 2.9.3: the segment homotopy ends at the second projection. -/
lemma sphere_segment_map_one (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_segment_map n (1, pq) = sphere_second_projection n pq := by
  -- Unwrap the `ULift` and use the `t = 1` endpoint computation.
  apply ULift.ext
  change sphere_segment_point n 1 pq.1.1 pq.1.2 pq.2 zero_le_one le_rfl = pq.1.2.down
  exact sphere_segment_point_one n pq.1.1 pq.1.2 pq.2

/-- Helper for Problem 2.9.3: the normalized segment gives a homotopy from the first projection to
the second projection. -/
def sphere_second_coordinate_homotopy (n : ℕ) :
    (sphere_first_projection n).Homotopy (sphere_second_projection n) where
  toContinuousMap := sphere_segment_map n
  map_zero_left := sphere_segment_map_zero n
  map_one_left := sphere_segment_map_one n

/-- Helper for Problem 2.9.3: the product deformation keeps the first coordinate fixed and moves
the second coordinate along the normalized segment. -/
def sphere_pair_deformation_product_map (n : ℕ) :
    C(unitInterval × nonantipodal_pair_space n, 𝕊 n × 𝕊 n) :=
  ((sphere_first_projection n).comp ContinuousMap.snd).prodMk (sphere_segment_map n)

/-- Helper for Problem 2.9.3: the product deformation always lands back in the non-antipodal
subspace. -/
lemma sphere_pair_deformation_product_map_mem (n : ℕ) (x : unitInterval × nonantipodal_pair_space n) :
    (sphere_pair_deformation_product_map n x).1.down ≠ -(sphere_pair_deformation_product_map n x).2.down := by
  -- This is exactly the non-antipodality lemma for the normalized segment.
  change x.2.1.1.down ≠ -(sphere_segment_raw_map n x)
  intro hneg
  have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
    simpa [eq_comm] using congrArg Neg.neg hneg
  exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
    simpa [sphere_segment_raw_map, sphere_segment_point] using hneg')

/-- Helper for Problem 2.9.3: the fixed-first-coordinate deformation is pointwise non-antipodal. -/
lemma sphere_pair_deformation_nonantipodal (n : ℕ) (x : unitInterval × nonantipodal_pair_space n) :
    x.2.1.1.down ≠ -(sphere_segment_map n x).down := by
  -- This is exactly the same normalization argument as above, specialized to the fixed first
  -- coordinate.
  intro hneg
  have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
    simpa [sphere_segment_map, sphere_segment_raw_map, eq_comm] using congrArg Neg.neg hneg
  exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
    simpa [sphere_segment_raw_map, sphere_segment_point] using hneg')

/-- Helper for Problem 2.9.3: the product deformation viewed as a continuous map into the
non-antipodal pair space. -/
def sphere_pair_deformation_map (n : ℕ) :
    C(unitInterval × nonantipodal_pair_space n, nonantipodal_pair_space n) := by
  refine
    { toFun := fun x ↦ ?_
      continuous_toFun := ?_ }
  let q : 𝕊 n := sphere_segment_map n x
  refine ⟨(x.2.1.1, q), ?_⟩
  intro hneg
  have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
    simpa [q, sphere_segment_map, sphere_segment_raw_map, eq_comm] using congrArg Neg.neg hneg
  exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
    simpa [q, sphere_segment_raw_map, sphere_segment_point] using hneg')
  exact Continuous.subtype_mk
    (show Continuous fun x : unitInterval × nonantipodal_pair_space n =>
      (x.2.1.1, sphere_segment_map n x) by
      fun_prop)
    (fun x ↦ by
      intro hneg
      have hneg' : sphere_segment_raw_map n x = -x.2.1.1.down := by
        simpa [sphere_segment_map, sphere_segment_raw_map, eq_comm] using congrArg Neg.neg hneg
      exact sphere_segment_point_ne_neg_left n x.2.2 x.1.2.1 x.1.2.2 (by
        simpa [sphere_segment_raw_map, sphere_segment_point] using hneg'))

/-- Helper for Problem 2.9.3: the product deformation starts at the diagonal of the first
projection. -/
lemma sphere_pair_deformation_zero (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_pair_deformation_map n (0, pq) =
      ((sphere_diagonal_map n).comp (sphere_first_projection n)) pq := by
  -- Compare the underlying pair and then use the `t = 0` endpoint for the moving coordinate.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simpa [sphere_pair_deformation_map, sphere_pair_deformation_product_map, sphere_diagonal_map]
      using sphere_segment_map_zero n pq

/-- Helper for Problem 2.9.3: the product deformation ends at the identity map. -/
lemma sphere_pair_deformation_one (n : ℕ) (pq : nonantipodal_pair_space n) :
    sphere_pair_deformation_map n (1, pq) = ContinuousMap.id (nonantipodal_pair_space n) pq := by
  -- Again compare the underlying pair and use the `t = 1` endpoint for the moving coordinate.
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · simpa [sphere_pair_deformation_map, sphere_pair_deformation_product_map, sphere_second_projection]
      using sphere_segment_map_one n pq

/-- Helper for Problem 2.9.3: the first projection is a right homotopy inverse to the diagonal
map. -/
def sphere_first_projection_right_homotopy (n : ℕ) :
    ((sphere_diagonal_map n).comp (sphere_first_projection n)).Homotopy
      (ContinuousMap.id (nonantipodal_pair_space n)) where
  toContinuousMap := sphere_pair_deformation_map n
  map_zero_left := sphere_pair_deformation_zero n
  map_one_left := sphere_pair_deformation_one n

-- Proof sketch: a homotopy inverse is given by the normalized midpoint map
-- `(p, q) ↦ (p + q) / ‖p + q‖`;
-- the condition `p ≠ -q` ensures the midpoint is defined, and straight-line normalization gives the
-- two required homotopies.
/-- Problem 2.9.3: the diagonal map `p ↦ (p, p)` from `S^n` to the space of non-antipodal pairs in
`S^n × S^n` is the forward map of a homotopy equivalence. -/
theorem sphere_diagonal_map_homotopy_equiv (n : ℕ) :
    ∃ e : 𝕊 n ≃ₕ nonantipodal_pair_space n,
      e.toFun = sphere_diagonal_map n := by
  -- Route correction: keeping the first coordinate fixed makes the inverse exactly the first
  -- projection, and the normalized segment supplies the required right homotopy.
  refine ⟨{ toFun := sphere_diagonal_map n
            invFun := sphere_first_projection n
            left_inv := ?_
            right_inv := ⟨sphere_first_projection_right_homotopy n⟩ }, rfl⟩
  -- The left inverse is definitional once we project a diagonal pair.
  refine ⟨(ContinuousMap.Homotopy.refl (ContinuousMap.id (𝕊 n))).cast ?_ rfl⟩
  ext p
  rfl

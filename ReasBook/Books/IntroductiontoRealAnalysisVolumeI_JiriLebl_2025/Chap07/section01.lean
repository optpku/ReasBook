/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators RealInnerProductSpace

universe u

section Chap07
section Section01

/-- Definition 7.1.1: A metric on a set `X` is a function
`d : X × X → ℝ` satisfying (i) `d x y ≥ 0` (nonnegativity),
(ii) `d x y = 0` iff `x = y` (identity of indiscernibles),
(iii) `d x y = d y x` (symmetry), and (iv)
`d x z ≤ d x y + d y z` (triangle inequality). The pair `(X, d)` is a
metric space. -/
structure MetricAxioms (X : Type u) (d : X → X → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  eq_zero : ∀ x y, d x y = 0 ↔ x = y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z

/-- A mathlib `MetricSpace` structure satisfies the book's metric axioms. -/
lemma metricSpace_metricAxioms (X : Type u) [MetricSpace X] :
    MetricAxioms X (fun x y => dist x y) := by
  refine ⟨?nonneg, ?eq_zero, ?symm, ?triangle⟩
  · intro x y
    simp
  · intro x y
    simp
  · intro x y
    simpa using (dist_comm (x := x) (y := y))
  · intro x y z
    simpa using dist_triangle x y z

/-- The metric axioms ensure there is a corresponding mathlib `MetricSpace`
whose distance is the given function. -/
theorem metricAxioms_iff_metricSpace (X : Type u) (d : X → X → ℝ) :
    MetricAxioms X d ↔ ∃ inst : MetricSpace X, inst.dist = d := by
  constructor
  · intro h
    classical
    let inst : MetricSpace X :=
      { dist := d
        dist_self := by
          intro x
          exact (h.eq_zero x x).2 rfl
        dist_comm := h.symm
        dist_triangle := h.triangle
        eq_of_dist_eq_zero := by
          intro x y hxy
          exact (h.eq_zero x y).1 hxy }
    exact ⟨inst, rfl⟩
  · rintro ⟨inst, hdist⟩
    subst hdist
    let _ : MetricSpace X := inst
    simpa using (metricSpace_metricAxioms (X := X))

/-- Example 7.1.2: The standard metric on `ℝ` is given by `d x y = |x - y|`,
and with this metric `ℝ` is a metric space. -/
theorem real_standard_metric (x y : ℝ) : dist x y = |x - y| := by
  simpa [Real.norm_eq_abs] using (dist_eq_norm (x) (y))

/-- Example 7.1.3: On `ℝ` we can define a nonstandard metric
`d x y = |x - y| / (|x - y| + 1)`, which is symmetric, vanishes on the
diagonal, satisfies the triangle inequality, and is bounded by `1`, so every
pair of points is at distance `< 1`. -/
noncomputable def realNonstandardDist (x y : ℝ) : ℝ :=
  |x - y| / (|x - y| + 1)

lemma realNonstandardDist_metric_axioms :
    (∀ x y, 0 ≤ realNonstandardDist x y) ∧
      (∀ x, realNonstandardDist x x = 0) ∧
      (∀ x y, realNonstandardDist x y = realNonstandardDist y x) ∧
      (∀ x y z, realNonstandardDist x z ≤
        realNonstandardDist x y + realNonstandardDist y z) ∧
      (∀ x y, realNonstandardDist x y < 1) := by
  refine ⟨?nonneg, ?diag, ?symm, ?tri, ?lt1⟩
  · intro x y
    have hnum : 0 ≤ |x - y| := abs_nonneg _
    have hden : 0 ≤ |x - y| + 1 := by nlinarith
    exact div_nonneg hnum hden
  · intro x
    simp [realNonstandardDist]
  · intro x y
    simp [realNonstandardDist, abs_sub_comm]
  · intro x y z
    -- Auxiliary monotonicity of `t ↦ t / (t + 1)` on nonnegative reals.
    have phi_mono :
        ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ b →
          a / (a + 1) ≤ b / (b + 1) := by
      intro a b ha hb hab
      have ha1 : a + 1 ≠ 0 := by linarith
      have hb1 : b + 1 ≠ 0 := by linarith
      have hmul : a * (b + 1) ≤ b * (a + 1) := by nlinarith
      field_simp [ha1, hb1]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    -- Algebraic subadditivity `φ (a + b) ≤ φ a + φ b` for nonnegative `a b`.
    have phi_sub :
        ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b →
          (a + b) / (a + b + 1) ≤ a / (a + 1) + b / (b + 1) := by
      intro a b ha hb
      have hne1 : a + 1 ≠ 0 := by nlinarith
      have hne2 : b + 1 ≠ 0 := by nlinarith
      have hne3 : a + b + 1 ≠ 0 := by nlinarith
      have hcalc :
          0 ≤ a / (a + 1) + b / (b + 1) - (a + b) / (a + b + 1) := by
        field_simp [hne1, hne2, hne3]
        ring_nf
        nlinarith [ha, hb]
      linarith
    have hxz_le : |x - z| ≤ |x - y| + |y - z| := abs_sub_le _ _ _
    have hxz_nonneg : 0 ≤ |x - z| := abs_nonneg _
    have hsum_nonneg :
        0 ≤ |x - y| + |y - z| := by
      nlinarith [abs_nonneg (x - y), abs_nonneg (y - z)]
    have h1 :
        realNonstandardDist x z ≤
          (|x - y| + |y - z|) / (|x - y| + |y - z| + 1) := by
      simpa [realNonstandardDist] using
        (phi_mono (a := |x - z|) (b := |x - y| + |y - z|)
          hxz_nonneg hsum_nonneg hxz_le)
    have h2 :
        (|x - y| + |y - z|) / (|x - y| + |y - z| + 1) ≤
          realNonstandardDist x y + realNonstandardDist y z := by
      have hxy_nonneg : 0 ≤ |x - y| := abs_nonneg _
      have hyz_nonneg : 0 ≤ |y - z| := abs_nonneg _
      simpa [realNonstandardDist] using
        (phi_sub (a := |x - y|) (b := |y - z|) hxy_nonneg hyz_nonneg)
    exact h1.trans h2
  · intro x y
    have hpos : 0 < |x - y| + 1 := by nlinarith [abs_nonneg (x - y)]
    have hlt : |x - y| < |x - y| + 1 := by linarith
    have h := (div_lt_one hpos).2 hlt
    simpa [realNonstandardDist] using h

/-- Lemma 7.1.4 (Cauchy--Schwarz inequality): For vectors
`x = (x₁, x₂, …, xₙ)` and `y = (y₁, y₂, …, yₙ)` in `ℝⁿ`,
`((∑ₖ xₖ yₖ)²) ≤ (∑ₖ xₖ²)(∑ₖ yₖ²)`. -/
lemma cauchySchwarz_fin (n : ℕ) (x y : Fin n → ℝ) :
    (∑ k : Fin n, x k * y k) ^ 2 ≤
      (∑ k : Fin n, (x k) ^ 2) * (∑ k : Fin n, (y k) ^ 2) := by
  classical
  -- Apply Cauchy--Schwarz in `EuclideanSpace` and rewrite inner products/norms.
  set u : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  set v : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 y
  have hcs := real_inner_mul_inner_self_le (x := u) (y := v)
  have hinner :
      inner (𝕜 := ℝ) u v = ∑ k : Fin n, x k * y k := by
    simpa [u, v, dotProduct, mul_comm] using
      (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) (ι := Fin n) x y)
  have hnormx :
      ‖u‖ ^ 2 = ∑ k : Fin n, (x k) ^ 2 := by
    simpa [u, Real.norm_eq_abs] using
      (EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := Fin n) u)
  have hnormy :
      ‖v‖ ^ 2 = ∑ k : Fin n, (y k) ^ 2 := by
    simpa [v, Real.norm_eq_abs] using
      (EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := Fin n) v)
  have hcs' :
      (∑ k : Fin n, x k * y k) * (∑ k : Fin n, x k * y k) ≤
        (∑ k : Fin n, (x k) ^ 2) * (∑ k : Fin n, (y k) ^ 2) := by
    simpa [hinner, hnormx, hnormy] using hcs
  simpa [pow_two] using hcs'

/-- Example 7.1.5: The standard metric on `ℝⁿ` is
`d x y = √(∑ k, (x k - y k) ^ 2)`, and the triangle inequality follows from
the Cauchy--Schwarz inequality. -/
noncomputable def euclideanStandardDist (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.sqrt (∑ k : Fin n, (x k - y k) ^ 2)

lemma euclideanStandardDist_eq_dist (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    euclideanStandardDist n x y = dist x y := by
  classical
  have hnorm :
      ‖x - y‖ ^ 2 = ∑ k : Fin n, (x k - y k) ^ 2 := by
    simpa [Real.norm_eq_abs] using
      (EuclideanSpace.norm_sq_eq (𝕜 := ℝ) (n := Fin n) (x - y))
  calc
    euclideanStandardDist n x y
        = Real.sqrt (∑ k : Fin n, (x k - y k) ^ 2) := rfl
    _ = Real.sqrt (‖x - y‖ ^ 2) := by
      simpa using congrArg Real.sqrt hnorm.symm
    _ = |‖x - y‖| := by
      simp
    _ = ‖x - y‖ := by
      have hnonneg : 0 ≤ ‖x - y‖ := norm_nonneg _
      simp [abs_of_nonneg hnonneg]
    _ = dist x y := by
      simp [dist_eq_norm]

lemma euclideanStandardDist_triangle (n : ℕ)
    (x y z : EuclideanSpace ℝ (Fin n)) :
    euclideanStandardDist n x z ≤
      euclideanStandardDist n x y + euclideanStandardDist n y z := by
  simpa [euclideanStandardDist_eq_dist] using (dist_triangle x y z)

/-- Example 7.1.6: Viewing `ℂ` as `ℝ²`, the metric is the Euclidean one, so
`dist z₁ z₂ = |z₁ - z₂|`.  The complex modulus is
`|x + iy| = √(x^2 + y^2)`, and its square is `x^2 + y^2`. -/
lemma complex_dist_eq_abs (z₁ z₂ : ℂ) :
    dist z₁ z₂ = ‖z₁ - z₂‖ := by
  simpa using dist_eq_norm z₁ z₂

lemma complex_abs_sq (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  simpa [Complex.normSq, pow_two] using (Complex.sq_norm z)

/-- Example 7.1.7: On any set with decidable equality, the discrete distance
`d x y = 1` if `x ≠ y` and `d x x = 0` defines a metric.  In finite cases
this places every distinct pair at distance `1`; for infinite sets it still
provides a genuine metric space structure. -/
noncomputable def discreteDist {X : Type u} [DecidableEq X] (x y : X) : ℝ :=
  if x = y then 0 else 1

lemma discreteDist_nonneg {X : Type u} [DecidableEq X] (x y : X) :
    0 ≤ discreteDist x y := by
  by_cases h : x = y <;> simp [discreteDist, h]

lemma discreteDist_eq_zero_iff {X : Type u} [DecidableEq X] (x y : X) :
    discreteDist x y = 0 ↔ x = y := by
  by_cases h : x = y <;> simp [discreteDist, h]

lemma discreteDist_triangle {X : Type u} [DecidableEq X]
    (x y z : X) :
    discreteDist x z ≤ discreteDist x y + discreteDist y z := by
  classical
  by_cases hxz : x = z
  · subst hxz
    have h :=
      add_nonneg (discreteDist_nonneg (x := x) (y := y))
        (discreteDist_nonneg (x := y) (y := x))
    simpa [discreteDist] using h
  · have hxz' : discreteDist x z = 1 := by simp [discreteDist, hxz]
    by_cases hxy : x = y
    · have hyz : y ≠ z := by
        intro hyz; exact hxz (hxy.trans hyz)
      have hyz' : discreteDist y z = 1 := by simp [discreteDist, hyz]
      have hxy' : discreteDist x y = 0 := by simp [discreteDist, hxy]
      linarith [hxz', hxy', hyz']
    · have hxy' : discreteDist x y = 1 := by simp [discreteDist, hxy]
      by_cases hyz : y = z
      · have hyz' : discreteDist y z = 0 := by simp [discreteDist, hyz]
        linarith [hxz', hxy', hyz']
      · have hyz' : discreteDist y z = 1 := by simp [discreteDist, hyz]
        linarith [hxz', hxy', hyz']

lemma discreteDist_metricAxioms (X : Type u) [DecidableEq X] :
    MetricAxioms X (fun x y => discreteDist x y) := by
  classical
  refine ⟨?nonneg, ?eq_zero, ?symm, ?triangle⟩
  · intro x y
    exact discreteDist_nonneg (x := x) (y := y)
  · intro x y
    simpa using (discreteDist_eq_zero_iff (x := x) (y := y))
  · intro x y
    by_cases h : x = y <;> simp [discreteDist, h, eq_comm]
  · intro x y z
    simpa using (discreteDist_triangle (x := x) (y := y) (z := z))

theorem discreteDist_metric_space (X : Type u) [DecidableEq X] :
    ∃ inst : MetricSpace X,
      inst.dist = (fun x y : X => discreteDist x y) := by
  classical
  refine
    (metricAxioms_iff_metricSpace (X := X)
        (d := fun x y : X => discreteDist x y)).1 ?_
  exact discreteDist_metricAxioms (X := X)

/-- Example 7.1.8: On the space `C([a,b], ℝ)` of continuous real-valued
functions on the interval `[a,b]`, the metric is given by
`d f g = sup_{x ∈ [a,b]} |f x - g x|`, which agrees with the uniform norm
`‖f - g‖`. Whenever we view `C([a,b], ℝ)` as a metric space, this is the
understood distance. -/
lemma continuous_interval_dist_eq_uniform {a b : ℝ}
    (f g : ContinuousMap (Set.Icc a b) ℝ) :
    dist f g = ‖f - g‖ := by
  simpa using dist_eq_norm f g

/-- Example 7.1.9: On the unit sphere `S² ⊂ ℝ³`, the great circle distance
between two points is the angle between the lines from the origin, so if
`x = (x₁,x₂,x₃)` and `y = (y₁,y₂,y₃)`, then
`d x y = arccos (x₁ y₁ + x₂ y₂ + x₃ y₃)`.  This distance satisfies the usual
metric axioms (the triangle inequality requires more work).  On a sphere of
radius `r`, the distance scales to `r • θ`. -/
abbrev spherePoints (r : ℝ) :=
  {p : EuclideanSpace ℝ (Fin 3) // dist p 0 = r}

noncomputable def greatCircleDist
    (x y : spherePoints 1) : ℝ :=
  Real.arccos (inner (𝕜 := ℝ) (x : EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 3)))

lemma spherePoints_norm_eq_one (x : spherePoints 1) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
  have hx := x.property
  -- `dist` on a Euclidean space is the norm of the difference.
  rw [dist_eq_norm] at hx
  rw [sub_zero] at hx
  exact hx

lemma greatCircleDist_eq_angle (x y : spherePoints 1) :
    greatCircleDist x y =
      InnerProductGeometry.angle (x : EuclideanSpace ℝ (Fin 3))
        (y : EuclideanSpace ℝ (Fin 3)) := by
  have hx := spherePoints_norm_eq_one x
  have hy := spherePoints_norm_eq_one y
  simp [greatCircleDist, InnerProductGeometry.angle, hx, hy]

lemma greatCircleDist_triangle (x y z : spherePoints 1) :
    greatCircleDist x z ≤ greatCircleDist x y + greatCircleDist y z := by
  have h :=
    InnerProductGeometry.angle_le_angle_add_angle
      (x : EuclideanSpace ℝ (Fin 3))
      (y : EuclideanSpace ℝ (Fin 3))
      (z : EuclideanSpace ℝ (Fin 3))
  simpa [greatCircleDist_eq_angle] using h

lemma greatCircleDist_metric_axioms :
    (∀ x y : spherePoints 1, 0 ≤ greatCircleDist x y) ∧
      (∀ x : spherePoints 1, greatCircleDist x x = 0) ∧
      (∀ x y : spherePoints 1, greatCircleDist x y = greatCircleDist y x) ∧
      (∀ x y z : spherePoints 1, greatCircleDist x z ≤
        greatCircleDist x y + greatCircleDist y z) := by
  refine ⟨?nonneg, ?diag, ?symm, ?triangle⟩
  · intro x y
    have h := Real.arccos_nonneg (inner (𝕜 := ℝ)
      (x : EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 3)))
    simpa [greatCircleDist] using h
  · intro x
    have hxnorm :
        ‖(x : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
      have hx := x.property
      rw [dist_eq_norm] at hx
      rw [sub_zero] at hx
      exact hx
    have hinner :
        inner (𝕜 := ℝ) (x : EuclideanSpace ℝ (Fin 3))
          (x : EuclideanSpace ℝ (Fin 3)) = 1 := by
      have h := real_inner_self_eq_norm_sq (x : EuclideanSpace ℝ (Fin 3))
      nlinarith [h, hxnorm]
    calc
      greatCircleDist x x
          = Real.arccos
              (inner (𝕜 := ℝ) (x : EuclideanSpace ℝ (Fin 3))
                (x : EuclideanSpace ℝ (Fin 3))) := rfl
      _ = Real.arccos 1 := by rw [hinner]
      _ = 0 := Real.arccos_one
  · intro x y
    simp [greatCircleDist, real_inner_comm]
  · intro x y z
    -- The triangle inequality for the great circle distance is nontrivial.
    simpa using greatCircleDist_triangle x y z

/-- Scaling the great circle distance to a sphere of radius `r` by multiplying
the angular separation by `r`. -/
noncomputable def greatCircleDistOfRadius (r : ℝ)
    (x y : spherePoints r) : ℝ :=
  r * Real.arccos
    (inner (𝕜 := ℝ) (x : EuclideanSpace ℝ (Fin 3)) (y : EuclideanSpace ℝ (Fin 3)) / (r ^ 2))

/-- Proposition 7.1.10: For a metric space `(X, d)` and subset `Y ⊆ X`, the
restriction of the distance function to `Y × Y` defines a metric on `Y`. -/
def restricted_dist_metric {X : Type u} [MetricSpace X] (Y : Set X) :
    MetricSpace {x : X // x ∈ Y} := by
  infer_instance

/-- Definition 7.1.11: For a metric space `(X, d)` and subset `Y ⊆ X`, the
restriction of `d` to `Y × Y` endows `Y` with the subspace metric. -/
def subspaceMetric {X : Type u} [MetricSpace X] (Y : Set X) :
    MetricSpace {x : X // x ∈ Y} :=
  restricted_dist_metric Y

/-- The subspace metric agrees with the standard metric structure that `mathlib`
provides on the subtype `Y`. -/
lemma subspaceMetric_eq_subtype {X : Type u} [MetricSpace X] (Y : Set X) :
    subspaceMetric (X := X) Y =
      (inferInstance : MetricSpace {x : X // x ∈ Y}) := by
  rfl

/-- Definition 7.1.12: In a metric space `(X, d)`, a subset `S ⊆ X` is bounded
if there exists a point `p` and real number `B` with `dist p x ≤ B` for every
`x ∈ S`. The space itself is bounded when its entire underlying set is
bounded. -/
def boundedSubset {X : Type u} [MetricSpace X] (S : Set X) : Prop :=
  ∃ p : X, ∃ B : ℝ, ∀ x ∈ S, dist p x ≤ B

def boundedSpace {X : Type u} [MetricSpace X] : Prop :=
  boundedSubset (X := X) (S := Set.univ)

/-- The book's boundedness agrees with the standard bornological notion in a
metric space. -/
lemma boundedSubset_iff_isBounded {X : Type u} [MetricSpace X] [Nonempty X] (S : Set X) :
    boundedSubset (X := X) S ↔ Bornology.IsBounded S := by
  constructor
  · rintro ⟨p, B, hB⟩
    refine (Metric.isBounded_iff_subset_closedBall (c := p)).2 ?_
    refine ⟨B, ?_⟩
    intro x hx
    exact (Metric.mem_closedBall').2 (by simpa using hB x hx)
  · intro h
    classical
    obtain ⟨p⟩ := (inferInstance : Nonempty X)
    rcases (Metric.isBounded_iff_subset_closedBall (c := p)).1 h with ⟨B, hB⟩
    refine ⟨p, B, ?_⟩
    intro x hx
    exact (Metric.mem_closedBall').1 (hB hx)

end Section01
end Chap07

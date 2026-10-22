/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.ProofStep_1_7_6
import AlgebraicTopology_May_1999.Chap01.Lemma_1_7_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContinuousMap CircleDegree unitInterval BigOperators

variable (f : Polynomial ℂ)
variable (hf : ∀ z : ℂ, 1 ≤ ‖z‖ → Polynomial.eval z f ≠ 0)

/-- A polynomial with no zeros for `‖z‖ ≥ 1` is nonzero on the unit circle. -/
-- Proof sketch: every point `z : Circle` satisfies `‖(z : ℂ)‖ = 1`, so the hypothesis `hf`
-- applies directly to show `Polynomial.eval (z : ℂ) f ≠ 0`.
theorem polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk
    (hf : ∀ z : ℂ, 1 ≤ ‖z‖ → Polynomial.eval z f ≠ 0)
    (z : Circle) :
    Polynomial.eval (z : ℂ) f ≠ 0 := by
  -- Every point of `S¹` has norm `1`, so the outside-the-disk hypothesis applies on the boundary.
  exact hf z (by simp [Circle.norm_coe z])

/-- Helper for ProofStep 1.7.7: normalization is multiplicative on nonzero complex numbers. -/
-- Proof sketch: compare both circle points after coercing to `ℂ`, rewrite the denominator with
-- `‖x * a‖ = ‖x‖ * ‖a‖`, and clear denominators.
theorem complexDivNormCircle_mul (x a : ℂ) (hx : x ≠ 0) (ha : a ≠ 0) :
    complexDivNormCircle (x * a) (mul_ne_zero hx ha) =
      complexDivNormCircle x hx * complexDivNormCircle a ha := by
  -- Reduce the equality in `Circle` to the corresponding equality in `ℂ`.
  apply Subtype.ext
  change x * a / ‖x * a‖ = (x / ‖x‖) * (a / ‖a‖)
  rw [norm_mul]
  field_simp [hx, ha]
  simp

/-- Helper for ProofStep 1.7.7: right multiplication on `S¹` by a fixed phase is homotopic to the
identity map. -/
-- Proof sketch: choose a path in `S¹` from `c` to `1`, then multiply each point of the circle by
-- that moving phase.
theorem circle_mulRight_homotopic_id (c : Circle) :
    (ContinuousMap.mulRight c : C(Circle, Circle)).Homotopic (ContinuousMap.id Circle) := by
  refine ⟨{
    toFun := fun x ↦ x.2 * (PathConnectedSpace.somePath c 1) x.1
    continuous_toFun := by
      -- The homotopy is the pointwise product of the identity-in-space and the chosen path in time.
      simpa using
        continuous_snd.mul
          ((PathConnectedSpace.somePath c 1).continuous.comp continuous_fst)
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    -- At time `0`, the path contributes the phase `c`.
    simp [ContinuousMap.mulRight]
  · intro z
    -- At time `1`, the path contributes the neutral element.
    simp

/-- Helper for ProofStep 1.7.7: multiplying a polynomial by a nonzero constant rotates its
normalized boundary map by the corresponding constant phase. -/
-- Proof sketch: evaluate `p * C a` on the circle, separate the constant factor using
-- `Polynomial.eval_mul`, and apply multiplicativity of complex normalization.
theorem polynomialNormalizedBoundaryMap_mul_C_eq_mulRight
    (p : Polynomial ℂ) (hp : ∀ z : Circle, Polynomial.eval (z : ℂ) p ≠ 0)
    (a : ℂ) (ha : a ≠ 0) :
    polynomialNormalizedBoundaryMap (p * Polynomial.C a)
      (fun z ↦ by
        rw [Polynomial.eval_mul, Polynomial.eval_C]
        exact mul_ne_zero (hp z) ha) =
      (ContinuousMap.mulRight (complexDivNormCircle a ha)).comp
        (polynomialNormalizedBoundaryMap p hp) := by
  ext z
  -- Evaluate both sides pointwise and isolate the constant phase factor.
  simp [polynomialNormalizedBoundaryMap_apply, ContinuousMap.comp_apply, ContinuousMap.mulRight,
    Polynomial.eval_mul, Polynomial.eval_C, complexDivNormCircle_mul, ha, hp z]

-- The next helpers implement the textbook radial homotopy through a globally polynomial raw
-- formula, so continuity at `t = 0` is built into the definition instead of handled piecewise.
/-- Helper for ProofStep 1.7.7: the coefficient-expanded radial homotopy for a monic polynomial. -/
def monic_radial_raw_homotopy (f : Polynomial ℂ) : I × Circle → ℂ := fun p ↦
  (∑ i ∈ Finset.range f.natDegree,
      f.coeff i * ((p.2 : ℂ) ^ i) * ((((p.1 : ℝ) : ℂ)) ^ (f.natDegree - i))) +
    ((p.2 : ℂ) ^ f.natDegree)

/-- Helper for ProofStep 1.7.7: the raw radial homotopy is continuous on `I × S¹`. -/
-- Proof sketch: each summand is a polynomial expression in the coordinate maps `t` and `z`, so
-- continuity follows from continuity of powers, products, finite sums, and the final leading term.
theorem monic_radial_raw_homotopy_continuous (f : Polynomial ℂ) :
    Continuous (monic_radial_raw_homotopy f) := by
  -- The source proof uses the globally polynomial model to avoid any singularity at `t = 0`.
  simpa [monic_radial_raw_homotopy] using
    (by
      continuity : Continuous fun p : I × Circle ↦
        (∑ i ∈ Finset.range f.natDegree,
            f.coeff i * ((p.2 : ℂ) ^ i) * ((((p.1 : ℝ) : ℂ)) ^ (f.natDegree - i))) +
          ((p.2 : ℂ) ^ f.natDegree))

/-- Helper for ProofStep 1.7.7: away from `t = 0`, the raw homotopy equals the textbook expression
`t^n f(z / t)`. -/
-- Proof sketch: expand the monic polynomial as `X^n + ∑_{i < n} a_i X^i`, evaluate at `z / t`,
-- multiply by `t^n`, and then simplify each term with `pow_sub₀`.
theorem monic_radial_raw_homotopy_eval_eq
    (f : Polynomial ℂ) (hmonic : f.Monic) (t : I) (z : Circle)
    (ht : (((t : ℝ) : ℂ)) ≠ 0) :
    monic_radial_raw_homotopy f (t, z) =
      ((((t : ℝ) : ℂ)) ^ f.natDegree) * Polynomial.eval ((z : ℂ) / (((t : ℝ) : ℂ))) f := by
  let n := f.natDegree
  let tC : ℂ := ((t : ℝ) : ℂ)
  let zC : ℂ := (z : ℂ)
  change (∑ i ∈ Finset.range n, f.coeff i * zC ^ i * tC ^ (n - i)) + zC ^ n =
      tC ^ n * Polynomial.eval (zC / tC) f
  have hsum : f = Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (f.coeff i) * Polynomial.X ^ i := by
    -- Monicity isolates the leading term and leaves only the lower-degree coefficients in the sum.
    simpa [n] using hmonic.as_sum
  have h_eval0 :
      Polynomial.eval (zC / tC) f =
        Polynomial.eval (zC / tC)
          (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
    exact congrArg (Polynomial.eval (zC / tC)) hsum
  have h_eval :
      Polynomial.eval (zC / tC) f =
        (zC / tC) ^ n + ∑ i ∈ Finset.range n, f.coeff i * ((zC / tC) ^ i) := by
    -- Evaluate the monic decomposition term-by-term at `z / t`.
    calc
      Polynomial.eval (zC / tC) f =
          Polynomial.eval (zC / tC)
            (Polynomial.X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (f.coeff i) * Polynomial.X ^ i) := h_eval0
      _ =
          Polynomial.eval (zC / tC) (Polynomial.X ^ n) +
            Polynomial.eval (zC / tC)
              (∑ i ∈ Finset.range n, Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
              rw [Polynomial.eval_add]
      _ =
          (zC / tC) ^ n +
            ∑ i ∈ Finset.range n,
              Polynomial.eval (zC / tC) (Polynomial.C (f.coeff i) * Polynomial.X ^ i) := by
              rw [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum]
      _ = (zC / tC) ^ n + ∑ i ∈ Finset.range n, f.coeff i * ((zC / tC) ^ i) := by
              simp
  have h_rhs :
      tC ^ n * Polynomial.eval (zC / tC) f =
        zC ^ n + ∑ i ∈ Finset.range n, f.coeff i * zC ^ i * tC ^ (n - i) := by
    -- Multiply the evaluated decomposition by `t^n`, then simplify each term separately.
    rw [h_eval, mul_add, Finset.mul_sum]
    congr 1
    · calc
        tC ^ n * ((zC / tC) ^ n) = tC ^ n * (zC ^ n / tC ^ n) := by
          rw [div_pow]
        _ = zC ^ n * (tC ^ n * (tC ^ n)⁻¹) := by
          rw [div_eq_mul_inv]
          ring
        _ = zC ^ n := by
          have hcancel : tC ^ n * (tC ^ n)⁻¹ = 1 := by
            exact mul_inv_cancel₀ (pow_ne_zero _ ht)
          rw [hcancel]
          simp
    · refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        tC ^ n * (f.coeff i * ((zC / tC) ^ i)) = f.coeff i * (tC ^ n * ((zC / tC) ^ i)) := by
              ring
        _ = f.coeff i * (zC ^ i * tC ^ (n - i)) := by
          have hi_le : i ≤ n := Nat.le_of_lt (Finset.mem_range.mp hi)
          calc
            f.coeff i * (tC ^ n * ((zC / tC) ^ i)) =
                f.coeff i * (tC ^ n * (zC ^ i / tC ^ i)) := by
                  rw [div_pow]
            _ = f.coeff i * (zC ^ i * (tC ^ n * (tC ^ i)⁻¹)) := by
                  rw [div_eq_mul_inv]
                  ring
            _ = f.coeff i * (zC ^ i * tC ^ (n - i)) := by
                  rw [← pow_sub₀ tC ht hi_le]
        _ = f.coeff i * zC ^ i * tC ^ (n - i) := by
              ring
  rw [h_rhs, add_comm]

/-- Helper for ProofStep 1.7.7: the raw radial homotopy specializes at `t = 0` to the leading
power `z^n`. -/
-- Proof sketch: every lower-order summand contains a positive power of `t`, hence vanishes when
-- `t = 0`, leaving only the monic leading term.
theorem monic_radial_raw_homotopy_zero (f : Polynomial ℂ) (z : Circle) :
    monic_radial_raw_homotopy f (0, z) = (z : ℂ) ^ f.natDegree := by
  rw [monic_radial_raw_homotopy]
  have hsum :
      ∑ i ∈ Finset.range f.natDegree,
        f.coeff i * (z : ℂ) ^ i * ((((0 : I) : ℝ) : ℂ) ^ (f.natDegree - i)) = 0 := by
    -- Each lower-order term contains a strictly positive power of `0`, so the whole sum vanishes.
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hi_lt : i < f.natDegree := Finset.mem_range.mp hi
    have hsub : f.natDegree - i ≠ 0 := Nat.sub_ne_zero_of_lt hi_lt
    simp [hsub]
  rw [hsum]
  simp

/-- Helper for ProofStep 1.7.7: normalizing a power of a point on `S¹` recovers the same power in
`Circle`. -/
-- Proof sketch: both circle points have the same complex coordinate `(z : ℂ)^n`, so extensionality
-- identifies them.
theorem complexDivNormCircle_pow_circle (z : Circle) (n : ℕ) :
    complexDivNormCircle ((z : ℂ) ^ n) (pow_ne_zero n z.coe_ne_zero) = z ^ n := by
  -- Compare the two points of `Circle` through their underlying complex numbers.
  apply Subtype.ext
  change (z : ℂ) ^ n / ‖(z : ℂ) ^ n‖ = (z ^ n : Circle)
  simp

/-- Helper for ProofStep 1.7.7: the raw radial homotopy never vanishes under the exterior-root
hypothesis. -/
-- Proof sketch: at `t = 0` the raw value is `z^n`, which is nonzero on the circle; for `t ≠ 0`,
-- rewrite to `t^n f(z / t)` and apply `hf` to the point `z / t`, whose norm is `1 / t ≥ 1`.
theorem monic_radial_raw_homotopy_nonvanishing
    (f : Polynomial ℂ) (hmonic : f.Monic)
    (hf : ∀ w : ℂ, 1 ≤ ‖w‖ → Polynomial.eval w f ≠ 0) (p : I × Circle) :
    monic_radial_raw_homotopy f p ≠ 0 := by
  rcases p with ⟨t, z⟩
  by_cases ht : (((t : ℝ) : ℂ)) = 0
  · -- At `t = 0`, the leading monic term is the entire raw homotopy.
    have ht_zero : t = 0 := by
      apply Subtype.ext
      exact Complex.ofReal_eq_zero.mp ht
    have hraw : monic_radial_raw_homotopy f (t, z) = (z : ℂ) ^ f.natDegree := by
      simpa [ht_zero] using monic_radial_raw_homotopy_zero f z
    rw [hraw]
    exact pow_ne_zero f.natDegree z.coe_ne_zero
  · -- For `t ≠ 0`, return to the textbook formula and use the no-roots hypothesis.
    rw [monic_radial_raw_homotopy_eval_eq f hmonic t z ht]
    refine mul_ne_zero (pow_ne_zero _ ht) ?_
    apply hf ((z : ℂ) / (((t : ℝ) : ℂ)))
    have htR : (t : ℝ) ≠ 0 := by
      intro ht_zero
      apply ht
      simp [ht_zero]
    have htI : t ≠ 0 := by
      intro ht_zero
      apply htR
      exact congrArg (fun s : I ↦ (s : ℝ)) ht_zero
    have ht_pos : 0 < (t : ℝ) := unitInterval.pos_iff_ne_zero.2 htI
    -- The boundary point has norm `1`, so dividing by `t ∈ (0, 1]` moves it to norm at least `1`.
    rw [norm_div, Circle.norm_coe, Complex.norm_real, Real.norm_of_nonneg t.2.1]
    simpa [one_div] using (one_le_inv₀ ht_pos).2 t.2.2

/-- The normalized boundary map of a monic polynomial with no zeros for `‖z‖ ≥ 1` is homotopic to
the degree-`natDegree` power map on `S¹`. -/
-- Proof sketch: use the explicit homotopy extending the textbook formula
-- `k(x,t) = t^n f(x / t)` for `t > 0`, with `n = f.natDegree`, and define its value at `t = 0`
-- by the limiting monic leading term `x^n`. The hypothesis on zeros for `‖z‖ ≥ 1` ensures the
-- denominator never vanishes along the homotopy, so this gives a homotopy to
-- `(ContinuousMap.id Circle) ^ (f.natDegree : ℤ)`.
theorem polynomialNormalizedBoundaryMap_homotopic_id_zpow_of_monic_of_no_root_outside_open_unit_disk
    (hmonic : f.Monic) :
    (polynomialNormalizedBoundaryMap f
      (polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk f hf)).Homotopic
      ((ContinuousMap.id Circle) ^ (f.natDegree : ℤ)) := by
  -- Route correction: use the coefficient-expanded raw homotopy first, then normalize it; this
  -- keeps continuity at `t = 0` algebraic instead of forcing a piecewise definition.
  have H :
      (((ContinuousMap.id Circle) ^ (f.natDegree : ℤ))).Homotopy
        (polynomialNormalizedBoundaryMap f
          (polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk f hf)) :=
    { toFun := fun p ↦
        complexDivNormCircle
          (monic_radial_raw_homotopy f p)
          (monic_radial_raw_homotopy_nonvanishing f hmonic hf p)
      continuous_toFun := by
        let g : I × Circle → ℂ := monic_radial_raw_homotopy f
        have hg : Continuous g := monic_radial_raw_homotopy_continuous f
        have hnorm : Continuous fun p : I × Circle ↦ ((‖g p‖ : ℝ) : ℂ) :=
          Complex.continuous_ofReal.comp hg.norm
        -- The nonvanishing lemma keeps the normalization denominator away from zero.
        have hdiv : Continuous fun p : I × Circle ↦ g p / ‖g p‖ :=
          hg.div hnorm (fun p : I × Circle ↦ by
            exact_mod_cast norm_ne_zero_iff.2
              (monic_radial_raw_homotopy_nonvanishing f hmonic hf p))
        simpa [complexDivNormCircle, g] using
          (Continuous.subtype_mk hdiv
            (fun p : I × Circle ↦ mem_sphere_zero_iff_norm.2
              (complexDivNormCircle_norm_eq_one
                (g p)
                (monic_radial_raw_homotopy_nonvanishing f hmonic hf p))))
      map_zero_left := by
        intro z
        -- At `t = 0`, only the leading monic term survives, giving the power map.
        calc
          complexDivNormCircle
              (monic_radial_raw_homotopy f (0, z))
              (monic_radial_raw_homotopy_nonvanishing f hmonic hf (0, z)) =
            complexDivNormCircle ((z : ℂ) ^ f.natDegree) (pow_ne_zero f.natDegree z.coe_ne_zero) := by
              exact complexDivNormCircle_congr
                (monic_radial_raw_homotopy_zero f z)
                (monic_radial_raw_homotopy_nonvanishing f hmonic hf (0, z))
                (pow_ne_zero f.natDegree z.coe_ne_zero)
          _ = (((ContinuousMap.id Circle) ^ (f.natDegree : ℤ)) z) := by
              simpa [ContinuousMap.zpow_apply, ContinuousMap.id_apply] using
                complexDivNormCircle_pow_circle z f.natDegree
      map_one_left := by
        intro z
        -- At `t = 1`, the normalized raw homotopy recovers the original boundary map.
        change
          complexDivNormCircle
              (monic_radial_raw_homotopy f (1, z))
              (monic_radial_raw_homotopy_nonvanishing f hmonic hf (1, z)) =
            complexDivNormCircle (Polynomial.eval (z : ℂ) f)
              (polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk f hf z)
        have hraw :
            monic_radial_raw_homotopy f (1, z) = Polynomial.eval (z : ℂ) f := by
          simpa using
            monic_radial_raw_homotopy_eval_eq f hmonic 1 z (by norm_num : ((((1 : I) : ℝ) : ℂ)) ≠ 0)
        exact complexDivNormCircle_congr hraw
          (monic_radial_raw_homotopy_nonvanishing f hmonic hf (1, z))
          (polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk f hf z) }
  -- The explicit homotopy runs from the power map to the boundary map, so reverse it.
  exact ⟨H.symm⟩

/-- ProofStep 1.7.7: if a complex polynomial has no roots outside the open unit disk, then its
normalized boundary map `\hat f` on `S¹` has degree equal to the polynomial degree. -/
-- Proof sketch: set `g = f * Polynomial.C f.leadingCoeff⁻¹`. Then `g` is monic by the canonical
-- mathlib lemma `Polynomial.monic_mul_leadingCoeff_inv`, and `g` has the same `natDegree` as `f`
-- by `Polynomial.natDegree_mul_leadingCoeff_inv`. Since `f = g * Polynomial.C f.leadingCoeff`,
-- the normalized boundary maps of `f` and `g` differ by pointwise multiplication with a constant
-- circle-valued map, whose degree is `0` by `circleDegree_const`; hence they have the same degree.
-- Apply the monic homotopy theorem to `g`, use homotopy invariance via
-- `circleDegree_eq_of_homotopic`, and finish with `circleDegree_id_zpow`.
theorem circleDegree_polynomialNormalizedBoundaryMap_eq_natDegree_of_no_root_outside_open_unit_disk :
    deg(polynomialNormalizedBoundaryMap f
      (polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk f hf)) =
      (f.natDegree : ℤ) := by
  let hfCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0 :=
    polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk f hf
  have hf_eval_one : Polynomial.eval (1 : ℂ) f ≠ 0 := hf 1 (by norm_num)
  have hfnz : f ≠ 0 := by
    -- Evaluate at `1` to rule out the zero polynomial.
    intro hzero
    simp [hzero] at hf_eval_one
  have hlead : f.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hfnz
  let g : Polynomial ℂ := f * Polynomial.C f.leadingCoeff⁻¹
  have hgCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) g ≠ 0 := by
    intro z
    -- Rescaling by a nonzero constant preserves boundary nonvanishing.
    dsimp [g]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero (hfCircle z) (inv_ne_zero hlead)
  have hgOutside : ∀ z : ℂ, 1 ≤ ‖z‖ → Polynomial.eval z g ≠ 0 := by
    intro z hz
    -- The same rescaling preserves nonvanishing on the whole exterior region.
    dsimp [g]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    exact mul_ne_zero (hf z hz) (inv_ne_zero hlead)
  have hmonic : g.Monic := by
    -- Normalize `f` by its leading coefficient to reach the monic case.
    dsimp [g]
    simpa using Polynomial.monic_mul_leadingCoeff_inv hfnz
  have hnatDegree : g.natDegree = f.natDegree := by
    -- Multiplying by the inverse leading coefficient does not change the degree.
    dsimp [g]
    simpa using Polynomial.natDegree_mul_leadingCoeff_inv f hfnz
  have hcompare :
      (polynomialNormalizedBoundaryMap g hgCircle).Homotopic
        (polynomialNormalizedBoundaryMap f hfCircle) := by
    -- The normalized boundary maps differ only by a constant phase rotation.
    rw [polynomialNormalizedBoundaryMap_mul_C_eq_mulRight]
    simpa using
      ContinuousMap.Homotopic.comp
        (circle_mulRight_homotopic_id
          (complexDivNormCircle f.leadingCoeff⁻¹ (inv_ne_zero hlead)))
        (ContinuousMap.Homotopic.refl (polynomialNormalizedBoundaryMap f hfCircle))
  have hmonicHomotopy :
      (polynomialNormalizedBoundaryMap g hgCircle).Homotopic
        ((ContinuousMap.id Circle) ^ (f.natDegree : ℤ)) := by
    -- Apply the monic case to the normalized polynomial `g`.
    simpa [hnatDegree] using
      polynomialNormalizedBoundaryMap_homotopic_id_zpow_of_monic_of_no_root_outside_open_unit_disk
        g hgOutside hmonic
  have hfinal :
      (polynomialNormalizedBoundaryMap f hfCircle).Homotopic
        ((ContinuousMap.id Circle) ^ (f.natDegree : ℤ)) := by
    -- Undo the constant phase rotation, then use the monic homotopy.
    refine ContinuousMap.Homotopic.trans ?_ hmonicHomotopy
    exact ContinuousMap.Homotopic.symm hcompare
  calc
    deg(polynomialNormalizedBoundaryMap f hfCircle) =
        deg((ContinuousMap.id Circle) ^ (f.natDegree : ℤ)) :=
      circleDegree_eq_of_homotopic _ _ hfinal
    _ = (f.natDegree : ℤ) := circleDegree_id_zpow _

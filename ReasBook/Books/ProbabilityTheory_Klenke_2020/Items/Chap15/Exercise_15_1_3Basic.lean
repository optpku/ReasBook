/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_10

open MeasureTheory

open scoped BigOperators
open scoped Pointwise
open scoped RealInnerProductSpace

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Helper for Exercise 15.1.3: the coordinate half-open cube `(-1 / 2, 1 / 2]^d`. -/
abbrev coordinateHalfCube (d : ℕ) : Set (Fin d → ℝ) :=
  {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)}

/-- Helper for Exercise 15.1.3: the coordinate cube `(-π, π]^d`. -/
abbrev coordinatePiIocCube (d : ℕ) : Set (Fin d → ℝ) :=
  {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ioc (-Real.pi) Real.pi}

/-- Helper for Exercise 15.1.3: the coordinate cube `[-π, π)^d`. -/
abbrev coordinatePiIcoCube (d : ℕ) : Set (Fin d → ℝ) :=
  {y : Fin d → ℝ | ∀ i, y i ∈ Set.Ico (-Real.pi) Real.pi}

/-- Helper for Exercise 15.1.3: the torus chart is taken over the coordinate cube
`(-1 / 2, 1 / 2]^d`. -/
abbrev latticeTorusChartBase (d : ℕ) : Fin d → ℝ := fun _ ↦ -(1 / 2 : ℝ)

/-- Helper for Exercise 15.1.3: the lattice characteristic function pulled back to the torus
through the standard `(-1 / 2, 1 / 2]^d` chart. -/
abbrev latticeTorusChartRescaled (d : ℕ) :
    UnitAddTorus (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun u ↦
    (2 * Real.pi) •
      WithLp.toLp 2 ((UnitAddTorus.measurableEquivPiIoc (latticeTorusChartBase d) u).1)

/-- Helper for Exercise 15.1.3: the rescaled torus chart is measurable. -/
lemma latticeTorusChartRescaled_measurable {d : ℕ} :
    Measurable (latticeTorusChartRescaled d) := by
  -- Proof comment: the torus chart, subtype projection, `WithLp.toLp`, and scalar multiplication
  -- are all measurable, so the composite is measurable by `fun_prop`.
  fun_prop

/-- Helper for Exercise 15.1.3: `latticeTorusChar` is `charFun` composed with the rescaled torus
chart. -/
def latticeTorusChar {d : ℕ} (μ : Measure (Fin d → ℤ)) : UnitAddTorus (Fin d) → ℂ :=
  fun u ↦ charFun (μ.map latticeEmbedding) (latticeTorusChartRescaled d u)

/-- Helper for Exercise 15.1.3: on `(-1 / 2, 1 / 2]^d`, the torus chart returns the original
coordinate vector. -/
lemma measurableEquivPiIoc_apply_halfCube {d : ℕ} {y : Fin d → ℝ}
    (hy : y ∈ coordinateHalfCube d) :
    (UnitAddTorus.measurableEquivPiIoc (latticeTorusChartBase d)
      (fun i ↦ (y i : UnitAddCircle))).1 = y := by
  ext i
  simpa [UnitAddTorus.coe_measurableEquivPiIoc_apply, latticeTorusChartBase] using
    congrArg Subtype.val
      (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := -(1 / 2 : ℝ)) (hy i))

/-- Helper for Exercise 15.1.3: on `(-1 / 2, 1 / 2]^d`, the rescaled torus chart is just scalar
multiplication by `2π`. -/
lemma latticeTorusChartRescaled_apply_halfCube {d : ℕ} {y : Fin d → ℝ}
    (hy : y ∈ coordinateHalfCube d) :
    latticeTorusChartRescaled d (fun i ↦ (y i : UnitAddCircle)) =
      (2 * Real.pi) • WithLp.toLp 2 y := by
  rw [latticeTorusChartRescaled, measurableEquivPiIoc_apply_halfCube hy]

/-- Helper for Exercise 15.1.3: on `(-1 / 2, 1 / 2]^d`, `latticeTorusChar` evaluates the lattice
characteristic function at the rescaled coordinate vector. -/
lemma latticeTorusChar_apply_halfCube {d : ℕ} (μ : Measure (Fin d → ℤ)) {y : Fin d → ℝ}
    (hy : y ∈ coordinateHalfCube d) :
    latticeTorusChar (d := d) μ (fun i ↦ (y i : UnitAddCircle)) =
      charFun (μ.map latticeEmbedding) ((2 * Real.pi) • WithLp.toLp 2 y) := by
  simp [latticeTorusChar, latticeTorusChartRescaled_apply_halfCube hy]

/-- Helper for Exercise 15.1.3: the torus monomial at frequency `-x` matches the lattice Fourier
kernel after rescaling the torus coordinates by `2π`. -/
lemma mFourierNegEvalEqLatticeKernel {d : ℕ} (x : Fin d → ℤ) (y : Fin d → ℝ) :
    UnitAddTorus.mFourier (-x) (fun i ↦ (y i : UnitAddCircle)) =
      Complex.exp (-((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding x⟫ : ℝ) * Complex.I)) :=
by
  -- Route correction: use the current `fourier_coe_apply` and an explicit `latticeEmbedding (-x)`
  -- rewrite instead of the stale `AddCircle.fourier_coe_apply` path from the broken support file.
  calc
    UnitAddTorus.mFourier (-x) (fun i ↦ (y i : UnitAddCircle))
        = ∏ i : Fin d,
            Complex.exp
              ((((((-x i : ℤ) : ℝ)) * (((2 * Real.pi) • WithLp.toLp 2 y) i)) * Complex.I)) := by
            -- Proof comment: rewrite the torus monomial coordinatewise on the standard real
            -- representatives of `UnitAddCircle`.
            simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
            refine Finset.prod_congr rfl ?_
            intro i hi
            rw [fourier_coe_apply]
            congr 1
            simp [smul_eq_mul]
            ring_nf
    _ = Complex.exp (((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding (-x)⟫ : ℝ) *
          Complex.I)) := by
          -- Proof comment: the product form is exactly the coordinate factorization of the lattice
          -- character at frequency `-x`.
          symm
          simpa using latticeCharacter_eq_coordProd ((2 * Real.pi) • WithLp.toLp 2 y) (-x)
    _ = Complex.exp (-((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding x⟫ : ℝ) *
          Complex.I)) := by
          -- Proof comment: replacing `-x` by `x` inserts the global minus sign in the phase.
          have hneg : latticeEmbedding (-x) = -(latticeEmbedding x) := by
            ext i
            simp [latticeEmbedding]
          have hinner :
              (⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding (-x)⟫ : ℝ) =
                -((⟪(2 * Real.pi) • WithLp.toLp 2 y, latticeEmbedding x⟫ : ℝ)) := by
            rw [hneg, inner_neg_right]
          simp [hinner]

/-- Helper for Exercise 15.1.3: rescaling the coordinate box `(-1 / 2, 1 / 2]^d` by `2π`
produces the Jacobian factor `((2π)^d)⁻¹` and the box `(-π, π]^d`. -/
lemma coordinateHalfOpenCubeRescaleIntegral {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (G : (Fin d → ℝ) → E) :
    ∫ x in coordinateHalfCube d,
      G ((2 * Real.pi) • x) ∂volume =
        (((2 * Real.pi : ℝ) ^ d)⁻¹) •
          ∫ x in coordinatePiIocCube d,
            G x ∂volume := by
  have hpos : 0 < (2 * Real.pi : ℝ) := by
    positivity
  have hscale :
      ((2 * Real.pi : ℝ) • (coordinateHalfCube d : Set (Fin d → ℝ))) = coordinatePiIocCube d := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      intro i
      rcases hy i with ⟨hylo, hyhi⟩
      constructor
      · -- Proof comment: a positive `2π` rescales the lower endpoint `-1 / 2` to `-π`.
        change -Real.pi < (2 * Real.pi) * y i
        nlinarith [Real.pi_pos, hylo]
      · -- Proof comment: the same scaling sends the upper endpoint `1 / 2` to `π`.
        change (2 * Real.pi) * y i ≤ Real.pi
        nlinarith [Real.pi_pos, hyhi]
    · intro hz
      refine ⟨fun i ↦ z i / (2 * Real.pi), ?_, ?_⟩
      · intro i
        rcases hz i with ⟨hzlo, hzhi⟩
        constructor
        · change -(1 / 2 : ℝ) < z i / (2 * Real.pi)
          rw [lt_div_iff₀ hpos]
          nlinarith
        · change z i / (2 * Real.pi) ≤ -(1 / 2 : ℝ) + 1
          rw [div_le_iff₀ hpos]
          nlinarith
      · ext i
        change (2 * Real.pi) * (z i / (2 * Real.pi)) = z i
        field_simp [hpos.ne']
  -- Route correction: rewrite the scaled set explicitly after the current `setIntegral_comp_smul`
  -- API, rather than relying on the stale set-scalar simplification from the old support file.
  calc
    ∫ x in coordinateHalfCube d, G ((2 * Real.pi) • x) ∂volume =
        (((2 * Real.pi : ℝ) ^ d)⁻¹) •
          ∫ x in ((2 * Real.pi : ℝ) • (coordinateHalfCube d : Set (Fin d → ℝ))),
            G x ∂volume := by
            simpa [coordinateHalfCube] using
              (MeasureTheory.Measure.setIntegral_comp_smul_of_pos
                (μ := (volume : Measure (Fin d → ℝ))) (f := G) (s := coordinateHalfCube d) hpos)
    _ = (((2 * Real.pi : ℝ) ^ d)⁻¹) • ∫ x in coordinatePiIocCube d, G x ∂volume := by
          rw [hscale]

/-- Helper for Exercise 15.1.3: the product boxes `(-π, π]^d` and `[-π, π)^d` differ only on a
coordinate boundary of volume zero. -/
lemma coordinatePiIocAeEqPiIco (d : ℕ) :
    coordinatePiIocCube d =ᵐ[(volume : Measure (Fin d → ℝ))] coordinatePiIcoCube d := by
  let μ : Fin d → Measure ℝ := fun _ ↦ volume
  have hIoc :
      coordinatePiIocCube d =ᵐ[Measure.pi μ] Set.Icc (fun _ : Fin d ↦ -Real.pi)
        (fun _ ↦ Real.pi) := by
    simpa [coordinatePiIocCube, μ, Set.pi, Set.mem_setOf_eq, Set.Icc, Pi.le_def] using
      (Measure.univ_pi_Ioc_ae_eq_Icc
        (μ := μ) (f := fun _ : Fin d ↦ -Real.pi) (g := fun _ ↦ Real.pi))
  have hIco :
      coordinatePiIcoCube d =ᵐ[Measure.pi μ] Set.Icc (fun _ : Fin d ↦ -Real.pi)
        (fun _ ↦ Real.pi) := by
    simpa [coordinatePiIcoCube, μ, Set.pi, Set.mem_setOf_eq, Set.Icc, Pi.le_def] using
      (Measure.univ_pi_Ico_ae_eq_Icc
        (μ := μ) (f := fun _ : Fin d ↦ -Real.pi) (g := fun _ ↦ Real.pi))
  -- Proof comment: both half-open boxes agree almost everywhere with the same closed cube.
  simpa [μ, MeasureTheory.volume_pi] using hIoc.trans hIco.symm

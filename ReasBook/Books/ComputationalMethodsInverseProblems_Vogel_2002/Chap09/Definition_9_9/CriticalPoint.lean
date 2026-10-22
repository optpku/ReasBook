/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Prop_9_8
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Theorem_9_4.KKT
public import Mathlib.Analysis.Calculus.FDeriv.WithLp

public section

noncomputable section

namespace NonnegativeOrthant

variable {n : ℕ}

/-- A critical point for the nonnegative-orthant problem satisfies feasibility,
gradient nonnegativity, and complementarity coordinatewise. -/
structure IsCriticalPoint
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) : Prop where
  feasible : ∀ i : Fin n, 0 ≤ f i
  gradientNonneg : ∀ i : Fin n, 0 ≤ gradient J f i
  complementarity : ∀ i : Fin n, f i * gradient J f i = 0

/-- Build a critical-point certificate from the three defining coordinatewise
conditions. -/
abbrev ofConditions
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (hFeasible : ∀ i : Fin n, 0 ≤ f i)
    (hGradientNonneg : ∀ i : Fin n, 0 ≤ gradient J f i)
    (hComplementarity : ∀ i : Fin n, f i * gradient J f i = 0) :
    IsCriticalPoint J f where
  feasible := hFeasible
  gradientNonneg := hGradientNonneg
  complementarity := hComplementarity

/-- A critical point is, in particular, feasible for problem `(9.16)`. -/
theorem IsCriticalPoint.mem_feasibleSet
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (h : IsCriticalPoint J f) :
    f ∈ feasibleSet n := by
  rw [NonnegativeOrthant.mem_feasibleSet]
  exact h.feasible

/-- If a coordinate of the gradient is strictly positive at a critical point,
then the corresponding coordinate of `f` vanishes. -/
theorem IsCriticalPoint.eq_zero_of_gradient_pos
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (h : IsCriticalPoint J f)
    {i : Fin n}
    (hgrad : 0 < gradient J f i) :
    f i = 0 := by
  refine (mul_eq_zero.mp (h.complementarity i)).resolve_right (ne_of_gt hgrad)

/-- Helper for Definition 9.9: the gradient of the coordinate constraint
`fun x ↦ x i` is the `i`-th standard basis vector. -/
private theorem coordinateConstraintGradient
    (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n)) :
    gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f =
      EuclideanSpace.single i (1 : ℝ) := by
  ext j
  change gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f j =
    (EuclideanSpace.single i (1 : ℝ)) j
  have hderiv :
      fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f =
        EuclideanSpace.proj i := by
    simpa [EuclideanSpace.proj] using
      (PiLp.hasFDerivAt_apply (p := 2) (E := fun _ : Fin n ↦ ℝ) f i).fderiv
  -- Compare the `j`-th coordinate with the derivative on the `j`-th basis vector.
  calc
    gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f j
      = inner ℝ (gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f)
          (EuclideanSpace.single j (1 : ℝ)) := by
          simpa using
            (EuclideanSpace.inner_single_right j (1 : ℝ)
              (gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f)).symm
    _ = fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f
          (EuclideanSpace.single j (1 : ℝ)) := by
          exact
            (inner_gradient_left (𝕜 := ℝ)
              (f := fun x : EuclideanSpace ℝ (Fin n) ↦ x i)
              (x := f)
              (y := EuclideanSpace.single j (1 : ℝ)))
    _ = EuclideanSpace.proj i (EuclideanSpace.single j (1 : ℝ)) := by
          rw [hderiv]
    _ = EuclideanSpace.single i (1 : ℝ) j := by
          by_cases hij : i = j
          · simp [EuclideanSpace.proj, EuclideanSpace.single, hij]
          · simp [EuclideanSpace.proj, EuclideanSpace.single, hij]

/-- Helper for Definition 9.9: the KKT stationarity sum for the orthant
constraints reproduces `gradient J f`. -/
private theorem orthantStationarity
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    gradient J f =
      ∑ i : Fin n, gradient J f i • gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f := by
  -- Expand `gradient J f` in the Euclidean basis and then replace basis vectors by the
  -- gradients of the coordinate constraints.
  calc
    gradient J f = ∑ i : Fin n, gradient J f i • EuclideanSpace.basisFun (Fin n) ℝ i := by
      simpa [EuclideanSpace.basisFun_repr] using
        ((EuclideanSpace.basisFun (Fin n) ℝ).sum_repr (gradient J f)).symm
    _ = ∑ i : Fin n, gradient J f i • EuclideanSpace.single i (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [EuclideanSpace.basisFun_apply]
    _ = ∑ i : Fin n, gradient J f i • gradient (fun x : EuclideanSpace ℝ (Fin n) ↦ x i) f := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [coordinateConstraintGradient (i := i) (f := f)]

/-- The orthant critical-point conditions are exactly the KKT conditions for the
constraint family `fun i x ↦ x i` with multiplier `fun i ↦ gradient J f i`. -/
theorem isCriticalPoint_iff_isMultiplier
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    IsCriticalPoint J f ↔
      KKT.IsMultiplier J (fun i x ↦ x i) f (fun i ↦ gradient J f i) := by
  constructor
  · intro h
    -- Repackage the orthant critical-point data as the four KKT clauses.
    refine KKT.ofConditions (orthantStationarity J f) ?_ ?_ ?_
    · exact h.gradientNonneg
    · exact h.feasible
    · intro i
      simpa [mul_comm] using h.complementarity i
  · intro h
    -- Read the KKT data back as feasibility, gradient nonnegativity, and complementarity.
    refine ofConditions h.primalFeasible h.dualNonneg ?_
    intro i
    simpa [mul_comm] using h.complementarity i

/-- A critical point for the orthant problem gives a KKT multiplier for the
orthant constraints. -/
theorem IsCriticalPoint.isMultiplier
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {f : EuclideanSpace ℝ (Fin n)}
    (h : IsCriticalPoint J f) :
    KKT.IsMultiplier J (fun i x ↦ x i) f (fun i ↦ gradient J f i) :=
  (isCriticalPoint_iff_isMultiplier J f).mp h

/-- `IsCriticalPoint J f` is equivalent to feasibility on the nonnegative
orthant together with gradient nonnegativity and complementarity. -/
theorem isCriticalPoint_iff
    (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    IsCriticalPoint J f ↔
      f ∈ feasibleSet n ∧
        (∀ i : Fin n, 0 ≤ gradient J f i) ∧
          (∀ i : Fin n, f i * gradient J f i = 0) := by
  constructor
  · intro h
    -- Expand the structure fields into the source-facing coordinate conditions.
    exact ⟨h.mem_feasibleSet, h.gradientNonneg, h.complementarity⟩
  · rintro ⟨hf, hgrad, hcomp⟩
    -- Turn feasible-set membership back into the coordinatewise feasibility field.
    refine ofConditions ?_ hgrad hcomp
    simpa [NonnegativeOrthant.mem_feasibleSet] using hf

/-- A feasible local minimizer of `(9.16)` on the nonnegative orthant is a
critical point in the sense of `NonnegativeOrthant.IsCriticalPoint`. -/
theorem isCriticalPoint_of_isLocalMinOn
    {J : EuclideanSpace ℝ (Fin n) → ℝ}
    {fStar : EuclideanSpace ℝ (Fin n)}
    (hJ : ContDiff ℝ 1 J)
    (hfStar : fStar ∈ feasibleSet n)
    (hmin : IsLocalMinOn J (feasibleSet n) fStar) :
    IsCriticalPoint J fStar :=
  ofConditions
    (coordinate_nonneg hfStar)
    (gradient_nonneg hJ hfStar hmin)
    (complementarity hJ hfStar hmin)

end NonnegativeOrthant

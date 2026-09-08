module

public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

public section

open scoped BigOperators

universe u v w

/-- A finite Taylor jet of order `m`, represented by one continuous multilinear
coefficient in each degree from `0` through `m`. -/
structure FiniteTaylorJet (𝕜 : Type u) (E : Type v) (F : Type w)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (m : ℕ) where
  coeff : (n : Fin (m + 1)) → E [×(n : ℕ)]→L[𝕜] F

namespace FiniteTaylorJet

variable {𝕜 : Type u} {E : Type v} {F : Type w}
variable [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜)

/-- Construct the order-`m` Taylor jet at `x` from factorial-normalized iterated
Fréchet derivatives. -/
noncomputable def ofFunction [CharZero 𝕜] (m : ℕ) (f : E → F) (x : E) :
    FiniteTaylorJet 𝕜 E F m where
  coeff n := ((n : ℕ).factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 (n : ℕ) f x

variable {𝕜}

/-- Evaluate a finite Taylor jet on the diagonal at an increment `h`. -/
def eval {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) (h : E) : F :=
  ∑ n, J.coeff n (fun _ ↦ h)

/-- Extract the ordinary one-variable coefficient of a jet whose source is its
scalar field. -/
def scalarCoeff {m : ℕ} (J : FiniteTaylorJet 𝕜 𝕜 F m) (n : Fin (m + 1)) : F :=
  J.coeff n (fun _ ↦ 1)

/-- A scalar jet coefficient is its multilinear coefficient evaluated on the
all-ones vector. -/
theorem scalarCoeff_apply {m : ℕ} (J : FiniteTaylorJet 𝕜 𝕜 F m)
    (n : Fin (m + 1)) :
    J.scalarCoeff n = J.coeff n (fun _ ↦ 1) := by
  rfl

/-- Extend a finite Taylor jet by zero to a formal multilinear series. -/
def toFormalMultilinearSeries {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) :
    FormalMultilinearSeries 𝕜 E F := fun n ↦
  if h : n < m + 1 then J.coeff ⟨n, h⟩ else 0

/-- The concrete remainder after evaluating a finite Taylor jet at `h`. -/
def remainder {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) (f : E → F) (x h : E) : F :=
  f (x + h) - J.eval h

/-- The coefficients constructed by `ofFunction` are the normalized iterated
Fréchet derivatives. -/
theorem coeff_ofFunction [CharZero 𝕜] (m : ℕ) (f : E → F) (x : E)
    (n : Fin (m + 1)) :
    (ofFunction 𝕜 m f x).coeff n =
      ((n : ℕ).factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 (n : ℕ) f x := by
  -- Reducing the structure projection exposes the coefficient assigned by `ofFunction`.
  rfl

/-- Evaluating a coefficient constructed by `ofFunction` evaluates the
corresponding factorial-normalized iterated Fréchet derivative. -/
theorem coeff_ofFunction_apply [CharZero 𝕜] (m : ℕ) (f : E → F) (x : E)
    (n : Fin (m + 1)) (v : Fin (n : ℕ) → E) :
    (ofFunction 𝕜 m f x).coeff n v =
      ((n : ℕ).factorial : 𝕜)⁻¹ • iteratedFDeriv 𝕜 (n : ℕ) f x v := by
  -- First identify the coefficient map, then evaluate its scalar multiple on `v`.
  rw [coeff_ofFunction, _root_.smul_apply]

/-- Evaluation is the finite sum of the diagonal coefficient values. -/
theorem eval_eq_sum {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) (h : E) :
    J.eval h = ∑ n, J.coeff n (fun _ ↦ h) := by
  -- Evaluation is defined by this finite diagonal sum.
  rfl

/-- The zero extension agrees with the jet coefficient in every degree at most
`m`. -/
theorem toFormalMultilinearSeries_coeff_of_le {m n : ℕ}
    (J : FiniteTaylorJet 𝕜 E F m) (hn : n ≤ m) :
    J.toFormalMultilinearSeries n = J.coeff ⟨n, Nat.lt_succ_iff.mpr hn⟩ := by
  -- In a retained degree, the zero extension selects the original coefficient.
  simp only [toFormalMultilinearSeries, dif_pos (Nat.lt_succ_iff.mpr hn)]

/-- The formal multilinear series associated to a finite jet vanishes in every
degree strictly above `m`. -/
theorem toFormalMultilinearSeries_coeff_of_lt {m n : ℕ}
    (J : FiniteTaylorJet 𝕜 E F m) (hn : m < n) :
    J.toFormalMultilinearSeries n = 0 := by
  -- A degree above the truncation bound is sent to zero.
  simp only [toFormalMultilinearSeries, dif_neg (Nat.not_lt.mpr hn)]

/-- Jet evaluation agrees with the canonical partial sum of its zero extension. -/
theorem eval_eq_partialSum {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) (h : E) :
    J.eval h = J.toFormalMultilinearSeries.partialSum (m + 1) h := by
  -- Reindex the partial sum by `Fin (m + 1)` and use the retained coefficients.
  rw [eval_eq_sum, FormalMultilinearSeries.partialSum, ← Fin.sum_univ_eq_sum_range]
  congr with n
  exact (congrArg (fun c ↦ c (fun _ ↦ h))
    (toFormalMultilinearSeries_coeff_of_le J (Nat.le_of_lt_succ n.isLt))).symm

/-- For a one-variable jet, evaluation is the power sum of its scalar
coefficients. -/
theorem eval_eq_sum_smul_scalarCoeff {m : ℕ} (J : FiniteTaylorJet 𝕜 𝕜 F m)
    (z : 𝕜) :
    J.eval z = ∑ n : Fin (m + 1), z ^ (n : ℕ) • J.scalarCoeff n := by
  -- Multilinearity extracts one factor of `z` from every coordinate.
  rw [eval_eq_sum]
  congr with n
  simpa only [scalarCoeff, Finset.prod_const, Finset.card_fin, smul_eq_mul, mul_one] using
    (J.coeff n).map_smul_univ (fun _ ↦ z) (fun _ ↦ 1)

/-- The scalar coefficients of `ofFunction` are normalized iterated
one-variable derivatives. -/
theorem scalarCoeff_ofFunction [CharZero 𝕜] (m : ℕ) (f : 𝕜 → F) (x : 𝕜)
    (n : Fin (m + 1)) :
    (ofFunction 𝕜 m f x).scalarCoeff n =
      ((n : ℕ).factorial : 𝕜)⁻¹ • iteratedDeriv (n : ℕ) f x := by
  -- Applying the iterated Fréchet derivative to the all-ones vector is `iteratedDeriv`.
  simp only [scalarCoeff, coeff_ofFunction, _root_.smul_apply,
    iteratedDeriv_eq_iteratedFDeriv]

/-- The remainder is the function value at `x + h` minus the evaluated jet. -/
theorem remainder_def {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m)
    (f : E → F) (x h : E) :
    J.remainder f x h = f (x + h) - J.eval h := by
  -- This is the defining subtraction for the concrete remainder.
  rfl

/-- A convergent analytic power series evaluates the derivative-constructed jet
as its corresponding finite partial sum. -/
theorem eval_of_hasFPowerSeriesOnBall [CharZero 𝕜] [CompleteSpace F]
    {m : ℕ} {f : E → F} {p : FormalMultilinearSeries 𝕜 E F}
    {x h : E} {r : ENNReal} (hf : HasFPowerSeriesOnBall f p x r) :
    (ofFunction 𝕜 m f x).eval h = p.partialSum (m + 1) h := by
  -- Put both sides over the same finite index set, then cancel the factorial degreewise.
  rw [eval_eq_sum, FormalMultilinearSeries.partialSum, ← Fin.sum_univ_eq_sum_range]
  congr with n
  rw [coeff_ofFunction, _root_.smul_apply, ← hf.factorial_smul h n,
    smul_comm, ← smul_assoc, nsmul_eq_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n : ℕ))), one_smul]

end FiniteTaylorJet

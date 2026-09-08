module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
public import Mathlib.Analysis.InnerProductSpace.Defs

public section

open scoped BigOperators

universe u v w x

namespace FiniteTaylorJet

variable {𝕜 : Type u} {E : Type v} {F : Type w} {G : Type x}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- The constant coefficient of a finite jet, obtained by evaluating it at the
zero increment. -/
def constantCoeff {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) : F :=
  J.eval 0

/-- The constant coefficient is evaluation at the zero increment. -/
theorem constantCoeff_apply {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) :
    J.constantCoeff = J.eval 0 := by
  -- Unfolding the projection exposes its defining evaluation.
  rfl

/-- Evaluation at zero retains exactly the degree-zero coefficient of a finite jet. -/
theorem constantCoeff_eq_coeff_zero {m : ℕ} (J : FiniteTaylorJet 𝕜 E F m) :
    J.constantCoeff = J.coeff (0 : Fin (m + 1)) (fun _ ↦ 0) := by
  -- Split off degree zero; multilinearity kills every positive-degree summand.
  rw [constantCoeff_apply, eval_eq_sum, Fin.sum_univ_succ]
  have htail : ∑ i : Fin m, J.coeff i.succ (fun _ ↦ 0) = 0 := by
    -- Each tail degree is positive, so its coordinate type is nonempty.
    apply Finset.sum_eq_zero
    intro i hi
    exact (J.coeff i.succ).map_coord_zero ⟨0, Nat.succ_pos (i : ℕ)⟩ rfl
  rw [htail, add_zero]

/-- The constant coefficient of the derivative-constructed jet is the value of
the function at its expansion base. -/
theorem constantCoeff_ofFunction [CharZero 𝕜] (m : ℕ) (f : E → F) (a : E) :
    (ofFunction 𝕜 m f a).constantCoeff = f a := by
  -- Reduce to degree zero, then evaluate the zeroth iterated Fréchet derivative.
  rw [constantCoeff_eq_coeff_zero, coeff_ofFunction, _root_.smul_apply]
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  exact iteratedFDeriv_zero_apply (fun _ ↦ 0)

/-- Truncate a formal multilinear series after degree `m`. -/
def truncate (m : ℕ) (p : FormalMultilinearSeries 𝕜 E F) :
    FiniteTaylorJet 𝕜 E F m where
  coeff n := p n

/-- Truncation retains every coefficient of degree at most `m`. -/
theorem coeff_truncate (m : ℕ) (p : FormalMultilinearSeries 𝕜 E F)
    (n : Fin (m + 1)) :
    (truncate m p).coeff n = p n := by
  -- Truncation stores the supplied formal-series coefficient unchanged.
  rfl

/-- Add two finite jets coefficientwise. -/
def add {m : ℕ} (P Q : FiniteTaylorJet 𝕜 E F m) :
    FiniteTaylorJet 𝕜 E F m :=
  truncate m (P.toFormalMultilinearSeries + Q.toFormalMultilinearSeries)

/-- Coefficients of a sum jet are sums of the corresponding coefficients. -/
theorem coeff_add {m : ℕ} (P Q : FiniteTaylorJet 𝕜 E F m)
    (n : Fin (m + 1)) :
    (add P Q).coeff n = P.coeff n + Q.coeff n := by
  -- Read the retained coefficient of each zero-extended series degreewise.
  rw [add, coeff_truncate, FormalMultilinearSeries.add_apply,
    toFormalMultilinearSeries_coeff_of_le P (Nat.le_of_lt_succ n.isLt),
    toFormalMultilinearSeries_coeff_of_le Q (Nat.le_of_lt_succ n.isLt)]

/-- Evaluation of a sum jet is the sum of the evaluations. -/
theorem eval_add {m : ℕ} (P Q : FiniteTaylorJet 𝕜 E F m) (h : E) :
    (add P Q).eval h = P.eval h + Q.eval h := by
  -- Distribute coefficientwise addition through diagonal evaluation and the finite sum.
  simp only [eval_eq_sum, coeff_add, add_apply, Finset.sum_add_distrib]

/-- Pair two finite jets coefficientwise. -/
def prod {m : ℕ} (P : FiniteTaylorJet 𝕜 E F m)
    (Q : FiniteTaylorJet 𝕜 E G m) : FiniteTaylorJet 𝕜 E (F × G) m :=
  truncate m (P.toFormalMultilinearSeries.prod Q.toFormalMultilinearSeries)

/-- Coefficients of a paired jet are Cartesian products of coefficients. -/
theorem coeff_prod {m : ℕ} (P : FiniteTaylorJet 𝕜 E F m)
    (Q : FiniteTaylorJet 𝕜 E G m) (n : Fin (m + 1)) :
    (prod P Q).coeff n = (P.coeff n).prod (Q.coeff n) := by
  -- Read the retained degree of the pointwise product formal series.
  rw [prod, coeff_truncate, FormalMultilinearSeries.prod,
    toFormalMultilinearSeries_coeff_of_le P (Nat.le_of_lt_succ n.isLt),
    toFormalMultilinearSeries_coeff_of_le Q (Nat.le_of_lt_succ n.isLt)]

/-- Compose two factorial-normalized finite jets and truncate the resulting
formal multilinear series at their common order. -/
def comp {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) : FiniteTaylorJet 𝕜 E G m :=
  truncate m (Q.toFormalMultilinearSeries.comp P.toFormalMultilinearSeries)

/-- A coefficient of a composed jet is the corresponding coefficient of the
normalized formal-series composition. -/
theorem coeff_comp {m : ℕ} (Q : FiniteTaylorJet 𝕜 F G m)
    (P : FiniteTaylorJet 𝕜 E F m) (n : Fin (m + 1)) :
    (comp Q P).coeff n =
      (Q.toFormalMultilinearSeries.comp P.toFormalMultilinearSeries) n := by
  -- Truncating the composition retains its coefficient in the requested degree.
  rfl

section RealPostcomposition

variable [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- Postcompose a real finite jet by the derivative-constructed finite jet of
an outer function at the inner jet's constant coefficient. -/
noncomputable def postcomp {m : ℕ} (g : F → G) (J : FiniteTaylorJet ℝ E F m) :
    FiniteTaylorJet ℝ E G m :=
  comp (ofFunction ℝ m g J.constantCoeff) J

/-- Analytic postcomposition is normalized formal-series composition with the
outer derivative jet. -/
theorem postcomp_def {m : ℕ} (g : F → G) (J : FiniteTaylorJet ℝ E F m) :
    postcomp g J = comp (ofFunction ℝ m g J.constantCoeff) J := by
  -- This equality unfolds the postcomposition construction.
  rfl

end RealPostcomposition

section AlgebraOperations

variable {A : Type w} [NormedRing A] [NormedAlgebra ℝ A]
variable [NormedSpace ℝ E]

/-- Multiply two algebra-valued finite jets by pairing them and postcomposing
with algebra multiplication. -/
noncomputable def mul {m : ℕ} (P Q : FiniteTaylorJet ℝ E A m) :
    FiniteTaylorJet ℝ E A m :=
  postcomp (fun z : A × A ↦ z.1 * z.2) (prod P Q)

/-- Multiplication of jets is postcomposition of their paired jet by algebra
multiplication. -/
theorem mul_def {m : ℕ} (P Q : FiniteTaylorJet ℝ E A m) :
    mul P Q = postcomp (fun z : A × A ↦ z.1 * z.2) (prod P Q) := by
  -- This equality unfolds the multiplication construction.
  rfl

end AlgebraOperations

section ScalarOperations

variable [NormedSpace ℝ E]

/-- The finite jet of reciprocal postcomposition. -/
noncomputable def inv {m : ℕ} (J : FiniteTaylorJet ℝ E ℝ m) :
    FiniteTaylorJet ℝ E ℝ m :=
  postcomp (fun z : ℝ ↦ z⁻¹) J

/-- Reciprocal jets are obtained by postcomposition with inversion. -/
theorem inv_def {m : ℕ} (J : FiniteTaylorJet ℝ E ℝ m) :
    inv J = postcomp (fun z : ℝ ↦ z⁻¹) J := by
  -- This equality unfolds reciprocal postcomposition.
  rfl

/-- The finite jet of real square-root postcomposition. -/
noncomputable def sqrt {m : ℕ} (J : FiniteTaylorJet ℝ E ℝ m) :
    FiniteTaylorJet ℝ E ℝ m :=
  postcomp Real.sqrt J

/-- Square-root jets are obtained by postcomposition with `Real.sqrt`. -/
theorem sqrt_def {m : ℕ} (J : FiniteTaylorJet ℝ E ℝ m) :
    sqrt J = postcomp Real.sqrt J := by
  -- This equality unfolds square-root postcomposition.
  rfl

end ScalarOperations

section NormOperation

variable [NormedSpace ℝ E] [InnerProductSpace ℝ F]

/-- The finite jet obtained by postcomposing an inner-product-space-valued jet
with its norm. -/
noncomputable def norm {m : ℕ} (J : FiniteTaylorJet ℝ E F m) :
    FiniteTaylorJet ℝ E ℝ m :=
  postcomp (fun z : F ↦ ‖z‖) J

/-- Norm jets are obtained by postcomposition with the norm function. -/
theorem norm_def {m : ℕ} (J : FiniteTaylorJet ℝ E F m) :
    norm J = postcomp (fun z : F ↦ ‖z‖) J := by
  -- This equality unfolds norm postcomposition.
  rfl

end NormOperation

/-- The order-`m` jet at zero of the weighted path `ε ↦ (ε, ε ^ 2)`. -/
noncomputable def weightedPathJet (m : ℕ) :
    FiniteTaylorJet ℝ ℝ (ℝ × ℝ) m :=
  ofFunction ℝ m (fun ε : ℝ ↦ (ε, ε ^ 2)) 0

/-- Coefficients of the weighted-path jet are its factorial-normalized iterated
Fréchet derivatives at zero. -/
theorem coeff_weightedPathJet (m : ℕ) (n : Fin (m + 1)) :
    (weightedPathJet m).coeff n =
      ((n : ℕ).factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ (n : ℕ) (fun ε : ℝ ↦ (ε, ε ^ 2)) 0 := by
  -- Unfold the weighted path jet and apply the constructor's coefficient law.
  exact coeff_ofFunction m (fun ε : ℝ ↦ (ε, ε ^ 2)) 0 n

end FiniteTaylorJet

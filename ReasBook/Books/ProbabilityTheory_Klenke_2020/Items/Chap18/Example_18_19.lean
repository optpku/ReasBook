/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

/-- Transition-matrix data for Example 18.19: the asymmetric nearest-neighbor random walk on the
finite discrete torus `Fin N` jumps one step to the right with probability `r` and one step to
the left with probability `1 - r`. When `N = 2`, the left and right targets coincide, so both
contributions are added. -/
def discrete_torus_walk_transition_matrix
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
      if j = (finRotate N).symm i then ENNReal.ofReal (1 - (r : ℝ)) else 0

/-- The torus walk transition matrix is the sum of the right-jump and left-jump masses on the two
adjacent torus neighbors. -/
theorem discrete_torus_walk_transition_matrix_apply
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    discrete_torus_walk_transition_matrix N r i j =
      (if j = finRotate N i then ENNReal.ofReal (r : ℝ) else 0) +
        if j = (finRotate N).symm i then ENNReal.ofReal (1 - (r : ℝ)) else 0 := rfl

/-- The canonical Markov-kernel view of the asymmetric torus walk on `Fin N`. -/
abbrev discrete_torus_walk_kernel
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (discrete_torus_walk_transition_matrix N r)

/-- The uniform distribution on the finite torus `Fin N`. -/
def discrete_torus_walk_uniform_distribution (N : ℕ) [NeZero N] :
    ProbabilityMeasure (Fin N) :=
  ⟨(PMF.uniformOfFintype (Fin N)).toMeasure, inferInstance⟩

/-- The torus walk transition matrix viewed over `ℂ` for Fourier spectral calculations. -/
def discrete_torus_walk_transition_matrix_complex
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j ↦ (discrete_torus_walk_transition_matrix N r i j).toReal

/-- The complex eigenvalue attached to the Fourier mode `k` for the asymmetric torus walk. -/
def discrete_torus_walk_eigenvalue
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (k : Fin N) : ℂ :=
  Real.cos (2 * Real.pi * (k : ℝ) / N) +
    ((2 * (r : ℝ) - 1) * Real.sin (2 * Real.pi * (k : ℝ) / N)) * Complex.I

/-- The odd-period contraction factor `γ = sqrt(1 - 4 r (1-r) sin(π / N)^2)`. -/
def discrete_torus_walk_convergence_factor
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  Real.sqrt (1 - 4 * (r : ℝ) * (1 - (r : ℝ)) * Real.sin (Real.pi / N) ^ 2)

/-- The lazy perturbation `p_ε = (1 - ε) p + ε I` of the asymmetric torus walk. -/
def lazy_discrete_torus_walk_transition_matrix
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j ↦
    ENNReal.ofReal (1 - (ε : ℝ)) * discrete_torus_walk_transition_matrix N r i j +
      if j = i then ENNReal.ofReal (ε : ℝ) else 0

/-- The lazy torus walk is the convex combination `(1 - ε) p + ε I`. -/
theorem lazy_discrete_torus_walk_transition_matrix_apply
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) (i j : Fin N) :
    lazy_discrete_torus_walk_transition_matrix N r ε i j =
      ENNReal.ofReal (1 - (ε : ℝ)) * discrete_torus_walk_transition_matrix N r i j +
        if j = i then ENNReal.ofReal (ε : ℝ) else 0 := rfl

/-- The canonical Markov-kernel view of the lazy torus walk. -/
abbrev lazy_discrete_torus_walk_kernel
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) : Kernel (Fin N) (Fin N) :=
  discreteMatrixKernel (lazy_discrete_torus_walk_transition_matrix N r ε)

/-- The lazy torus walk transition matrix viewed over `ℂ` for spectral calculations. -/
def lazy_discrete_torus_walk_transition_matrix_complex
    (N : ℕ) (r ε : Set.Ioo (0 : ℝ) 1) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j ↦ (lazy_discrete_torus_walk_transition_matrix N r ε i j).toReal

/-- The Fourier eigenvalue of the lazy torus walk at mode `k`. -/
def lazy_discrete_torus_walk_eigenvalue
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (ε : ℝ) (k : Fin N) : ℂ :=
  (1 - ε) * discrete_torus_walk_eigenvalue N r k + ε

/-- The threshold `ε₀` separating the two formulas for the second-largest modulus in the even
case. -/
def lazy_discrete_torus_walk_threshold
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : ℝ :=
  ((1 - (2 * (r : ℝ) - 1) ^ 2) * Real.sin (2 * Real.pi / N) ^ 2) /
    (((1 - (2 * (r : ℝ) - 1) ^ 2) * Real.sin (2 * Real.pi / N) ^ 2) +
      2 * Real.cos (2 * Real.pi / N))

/-- The modulus of the second largest eigenvalue of the lazy torus walk, written in the textbook's
piecewise form. -/
def lazy_discrete_torus_walk_second_modulus
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) (ε : ℝ) : ℝ :=
  if ε ≤ lazy_discrete_torus_walk_threshold N r then
    1 - 2 * ε
  else
    Real.sqrt
      (((1 - ε) * Real.cos (2 * Real.pi / N) + ε) ^ 2 +
        (((1 - ε) * (2 * (r : ℝ) - 1) * Real.sin (2 * Real.pi / N)) ^ 2))

/-- Example 18.19: `discrete_torus_walk_kernel N r` is aperiodic exactly when the torus size
`N` is odd. -/
def discrete_torus_walk_isAperiodic_iff_odd
    (N : ℕ) (r : Set.Ioo (0 : ℝ) 1) : Prop :=
  IsAperiodic (discrete_torus_walk_kernel N r) ↔ Odd N

end ProbabilityTheory

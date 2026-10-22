/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap03.Algorithm_3_2_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1.Blur2D
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.BTTB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_28
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.PosDef

public section

open scoped Matrix

namespace Blur2D

/-- The Section `8.3.2` two-dimensional benchmark uses the midpoint-sampled
translation-invariant PSF together with the corresponding observed image. -/
def IsMidpointTranslationInvariantBenchmark {n_x n_y : ℕ}
    (κ : (ℝ × ℝ) → ℝ) (Δx Δy : ℝ)
    (fExact η : Matrix (Fin n_x) (Fin n_y) ℝ)
    (t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (d : Matrix (Fin n_x) (Fin n_y) ℝ) : Prop :=
  t =
      sampledPSF (translationInvariantKernel κ) Δx Δy
        (fun a ↦ ((((a : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx))
        (fun b ↦ ((((b : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy)) ∧
    d = observedImage t fExact η

theorem IsMidpointTranslationInvariantBenchmark.sampledPSF_eq {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy : ℝ}
    {fExact η : Matrix (Fin n_x) (Fin n_y) ℝ}
    {t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ}
    {d : Matrix (Fin n_x) (Fin n_y) ℝ}
    (h : IsMidpointTranslationInvariantBenchmark κ Δx Δy fExact η t d) :
    t =
      sampledPSF (translationInvariantKernel κ) Δx Δy
        (fun a ↦ ((((a : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δx))
        (fun b ↦ ((((b : ℕ) : ℝ) + (1 / 2 : ℝ)) * Δy)) :=
  h.1

theorem IsMidpointTranslationInvariantBenchmark.observedImage_eq {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy : ℝ}
    {fExact η : Matrix (Fin n_x) (Fin n_y) ℝ}
    {t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ}
    {d : Matrix (Fin n_x) (Fin n_y) ℝ}
    (h : IsMidpointTranslationInvariantBenchmark κ Δx Δy fExact η t d) :
    d = observedImage t fExact η :=
  h.2

theorem IsMidpointTranslationInvariantBenchmark.kernel_eq {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy : ℝ}
    {fExact η : Matrix (Fin n_x) (Fin n_y) ℝ}
    {t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ}
    {d : Matrix (Fin n_x) (Fin n_y) ℝ}
    (h : IsMidpointTranslationInvariantBenchmark κ Δx Δy fExact η t d)
    (i μ : Fin n_x) (j ν : Fin n_y) :
    t i μ j ν =
      translationInvariantDiscretePSF κ Δx Δy
        (((i : ℕ) : ℤ) - ((μ : ℕ) : ℤ))
        (((j : ℕ) : ℤ) - ((ν : ℕ) : ℤ)) := by
  rw [h.sampledPSF_eq]
  simpa using sampledPSFMidpoint_eq_discretePSF κ Δx Δy i μ j ν

end Blur2D

namespace Matrix

/-- A finite array `c` is the Chapter 5 BCCB generating array cut out from the
integer-indexed kernel `t` on the base `Fin n_x × Fin n_y` window. Its
periodic extension is then the kernel whose HTTB matrix is `Matrix.bccb c`. -/
def IsBCCBGeneratingArray {n_x n_y : ℕ} (t : ℤ → ℤ → ℝ)
    (c : Matrix (Fin n_x) (Fin n_y) ℝ) : Prop :=
  ∀ i : Fin n_x, ∀ j : Fin n_y, c i j = t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ)

theorem IsBCCBGeneratingArray.apply {n_x n_y : ℕ} {t : ℤ → ℤ → ℝ}
    {c : Matrix (Fin n_x) (Fin n_y) ℝ} (h : IsBCCBGeneratingArray t c)
    (i : Fin n_x) (j : Fin n_y) :
    c i j = t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) :=
  h i j

theorem IsBCCBGeneratingArray.periodicExtension_apply {n_x n_y : ℕ}
    {h_x : 0 < n_x} {h_y : 0 < n_y} {t : ℤ → ℤ → ℝ}
    {c : Matrix (Fin n_x) (Fin n_y) ℝ} (h : IsBCCBGeneratingArray t c)
    (i : Fin n_x) (j : Fin n_y) :
    Matrix.periodicExtension h_x h_y c ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) =
      t ((i : ℕ) : ℤ) ((j : ℕ) : ℤ) := by
  rw [Matrix.periodicExtension_apply_natCast]
  exact h i j

end Matrix

/-- The Chapter 5 level-2 block circulant preconditioner for the Section `8.3.2`
benchmark replaces the BTTB blur and penalty blocks by the BCCB matrices
generated from their Chapter 5 block-circulant extension arrays. -/
def IsLevel2BlockCirculantPreconditioner {n_x n_y : ℕ}
    (κ : (ℝ × ℝ) → ℝ) (Δx Δy α : ℝ) (ℓ : ℤ → ℤ → ℝ)
    (cT cL : Matrix (Fin n_x) (Fin n_y) ℝ)
    (A M : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ) : Prop :=
  A =
      (Matrix.bttb n_x n_y (Blur2D.translationInvariantDiscretePSF κ Δx Δy))ᵀ *
          Matrix.bttb n_x n_y (Blur2D.translationInvariantDiscretePSF κ Δx Δy) +
        α • Matrix.bttb n_x n_y ℓ ∧
    Matrix.IsBCCBGeneratingArray (Blur2D.translationInvariantDiscretePSF κ Δx Δy) cT ∧
    Matrix.IsBCCBGeneratingArray ℓ cL ∧
    M = (Matrix.bccb cT)ᵀ * Matrix.bccb cT + α • Matrix.bccb cL

theorem IsLevel2BlockCirculantPreconditioner.system_eq {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy α : ℝ} {ℓ : ℤ → ℤ → ℝ}
    {cT cL : Matrix (Fin n_x) (Fin n_y) ℝ}
    {A M : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    (h : IsLevel2BlockCirculantPreconditioner κ Δx Δy α ℓ cT cL A M) :
    A =
      (Matrix.bttb n_x n_y (Blur2D.translationInvariantDiscretePSF κ Δx Δy))ᵀ *
          Matrix.bttb n_x n_y (Blur2D.translationInvariantDiscretePSF κ Δx Δy) +
        α • Matrix.bttb n_x n_y ℓ :=
  h.1

theorem IsLevel2BlockCirculantPreconditioner.blur_generatingArray {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy α : ℝ} {ℓ : ℤ → ℤ → ℝ}
    {cT cL : Matrix (Fin n_x) (Fin n_y) ℝ}
    {A M : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    (h : IsLevel2BlockCirculantPreconditioner κ Δx Δy α ℓ cT cL A M) :
    Matrix.IsBCCBGeneratingArray (Blur2D.translationInvariantDiscretePSF κ Δx Δy) cT :=
  h.2.1

theorem IsLevel2BlockCirculantPreconditioner.penalty_generatingArray {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy α : ℝ} {ℓ : ℤ → ℤ → ℝ}
    {cT cL : Matrix (Fin n_x) (Fin n_y) ℝ}
    {A M : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    (h : IsLevel2BlockCirculantPreconditioner κ Δx Δy α ℓ cT cL A M) :
    Matrix.IsBCCBGeneratingArray ℓ cL :=
  h.2.2.1

theorem IsLevel2BlockCirculantPreconditioner.preconditioner_eq {n_x n_y : ℕ}
    {κ : (ℝ × ℝ) → ℝ} {Δx Δy α : ℝ} {ℓ : ℤ → ℤ → ℝ}
    {cT cL : Matrix (Fin n_x) (Fin n_y) ℝ}
    {A M : Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ}
    (h : IsLevel2BlockCirculantPreconditioner κ Δx Δy α ℓ cT cL A M) :
    M = (Matrix.bccb cT)ᵀ * Matrix.bccb cT + α • Matrix.bccb cL :=
  h.2.2.2

/-
The Section `8.3.2` lagged-diffusivity or primal-dual Newton inner system
data on which the future faithful `Algorithm 3.2.2` PCG owner should act:
the Chapter 5 level-2 block circulant preconditioner together with the SPD
system/preconditioner hypotheses and the linear equation surface. -/
#check
  fun {n_x n_y : ℕ} (κ : (ℝ × ℝ) → ℝ) (Δx Δy α : ℝ)
    (A M : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (rhs solution : ℕ → EuclideanSpace ℝ (Fin n_y × Fin n_x))
    (ℓ : ℕ → ℤ → ℤ → ℝ) (cT cL : ℕ → Matrix (Fin n_x) (Fin n_y) ℝ) ↦
      ∀ v : ℕ,
        IsLevel2BlockCirculantPreconditioner κ Δx Δy α
          (ℓ v) (cT v) (cL v) (A v) (M v) ∧
          Matrix.PosDef (A v) ∧
          Matrix.PosDef (M v) ∧
          (A v).toEuclideanLin (solution v) = -rhs v

/-!
Exercise 8.15.

The source asks for the Section `8.3.2` two-dimensional benchmark to replace
the inner solves in the lagged-diffusivity and primal-dual Newton methods by
PCG together with the Chapter 5 level-2 block circulant preconditioner.

This file keeps the source-faithful benchmark and preconditioner owners above.
However, `Book.Ch3.Algorithm_3_2_2` is intentionally check-only because the
source payload omits the defining formula for the PCG update scalar `β_v`.
The repository therefore does not yet own a faithful PCG iterate surface.
Introducing local `Uses...PCG...` wrapper propositions here would guess the
missing iteration mathematics and would weaken the source meaning.

Accordingly the exercise-level PCG claim remains a labeled blocker/check-only
surface. The `#check` commands below record only the verified benchmark datum
owner, the Chapter 5 preconditioner owner, and the benchmark-specialized inner
system data on which a later faithful PCG owner should operate.
-/

/- Exercise 8.15. The Section `8.3.2` benchmark datum reused by the exercise. -/
#check Blur2D.IsMidpointTranslationInvariantBenchmark

/- Exercise 8.15. The Chapter 5 level-2 block circulant preconditioner reused
by the exercise. -/
#check IsLevel2BlockCirculantPreconditioner

/- Exercise 8.15. Main labeled source-facing blocker entry.

The concrete Section `8.3.2` benchmark owner and the Chapter 5 level-2 block
circulant preconditioner are already formalized above, but the actual PCG
iterate owner remains blocked upstream by `Book.Ch3.Algorithm_3_2_2`. This
`#check` therefore records only the verified exercise-specific ambient data for
the lagged-diffusivity and primal-dual Newton inner systems, rather than a
guessed “PCG solve” wrapper. -/
#check
  fun {n_x n_y : ℕ} (κ : (ℝ × ℝ) → ℝ) (Δx Δy α : ℝ)
    (fExact η : Matrix (Fin n_x) (Fin n_y) ℝ)
    (t : Fin n_x → Fin n_x → Fin n_y → Fin n_y → ℝ)
    (d : Matrix (Fin n_x) (Fin n_y) ℝ)
    (laggedA laggedM : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (laggedRhs laggedStep : ℕ → EuclideanSpace ℝ (Fin n_y × Fin n_x))
    (laggedℓ : ℕ → ℤ → ℤ → ℝ)
    (laggedCT laggedCL : ℕ → Matrix (Fin n_x) (Fin n_y) ℝ)
    (newtonA newtonM : ℕ → Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) ℝ)
    (newtonRhs deltaF : ℕ → EuclideanSpace ℝ (Fin n_y × Fin n_x))
    (newtonℓ : ℕ → ℤ → ℤ → ℝ)
    (newtonCT newtonCL : ℕ → Matrix (Fin n_x) (Fin n_y) ℝ) ↦
      Blur2D.IsMidpointTranslationInvariantBenchmark κ Δx Δy fExact η t d ∧
        (∀ v : ℕ,
          IsLevel2BlockCirculantPreconditioner κ Δx Δy α
            (laggedℓ v) (laggedCT v) (laggedCL v) (laggedA v) (laggedM v) ∧
            Matrix.PosDef (laggedA v) ∧
            Matrix.PosDef (laggedM v) ∧
            (laggedA v).toEuclideanLin (laggedStep v) = -laggedRhs v) ∧
        ∀ v : ℕ,
          IsLevel2BlockCirculantPreconditioner κ Δx Δy α
            (newtonℓ v) (newtonCT v) (newtonCL v) (newtonA v) (newtonM v) ∧
            Matrix.PosDef (newtonA v) ∧
            Matrix.PosDef (newtonM v) ∧
            (newtonA v).toEuclideanLin (deltaF v) = -newtonRhs v

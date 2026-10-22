/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Λ : Type u} {S : Type v} [Fintype S]

local instance : MeasurableSpace (Λ → S) := ⊤

/-- The configuration obtained from `x` by replacing its `i`-th coordinate by `σ`. This is the
source-facing operation written in the textbook as `x^{i,σ}`. -/
def gibbsCoordinateReplace (x : Λ → S) (i : Λ) (σ : S) : Λ → S :=
  let _ : DecidableEq Λ := Classical.decEq Λ
  Function.update x i σ

omit [Fintype S] in
@[simp] theorem gibbsCoordinateReplace_apply_same (x : Λ → S) (i : Λ) (σ : S) :
    gibbsCoordinateReplace x i σ i = σ := by
  simp [gibbsCoordinateReplace]

omit [Fintype S] in
@[simp] theorem gibbsCoordinateReplace_apply_ne (x : Λ → S) (i j : Λ) (σ : S) (hji : j ≠ i) :
    gibbsCoordinateReplace x i σ j = x j := by
  simp [gibbsCoordinateReplace, hji]

omit [Fintype S] in
@[simp] theorem gibbsCoordinateReplace_self (x : Λ → S) (i : Λ) :
    gibbsCoordinateReplace x i (x i) = x := by
  ext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [gibbsCoordinateReplace]

omit [Fintype S] in
private theorem gibbsCoordinateReplace_injective (x : Λ → S) (i : Λ) :
    Function.Injective (gibbsCoordinateReplace x i) := by
  intro σ τ hστ
  simpa using congrArg (fun y : Λ → S ↦ y i) hστ

omit [Fintype S] in
private theorem sameOutside_iff_eq_gibbsCoordinateReplace (x y : Λ → S) (i : Λ) :
    (∀ j : Λ, j ≠ i → y j = x j) ↔ y = gibbsCoordinateReplace x i (y i) := by
  constructor
  · intro h
    ext j
    by_cases hji : j = i
    · subst hji
      simp [gibbsCoordinateReplace]
    · simp [gibbsCoordinateReplace, h j hji, hji]
  · intro h j hji
    rw [h]
    simp [gibbsCoordinateReplace, hji]

/-- The mass that `π` assigns to the cylinder obtained by fixing all coordinates of `x` except the
`i`-th one. This is the source-facing quantity written in the textbook as `π(x_{-i})`. -/
def gibbsCoordinateMarginal (π : PMF (Λ → S)) (x : Λ → S) (i : Λ) : ℝ≥0∞ :=
  ∑' σ : S, π (gibbsCoordinateReplace x i σ)

/-- The single-site conditioning fibers of `π` are nonvanishing if every cylinder obtained by
fixing all coordinates except one has positive `π`-mass. Under this hypothesis, the textbook Gibbs
ratio formula is everywhere defined. -/
def HasPositiveGibbsCoordinateMarginals (π : PMF (Λ → S)) : Prop :=
  ∀ x : Λ → S, ∀ i : Λ, gibbsCoordinateMarginal π x i ≠ 0

private theorem gibbsCoordinateMarginal_ne_top (π : PMF (Λ → S)) (x : Λ → S) (i : Λ) :
    gibbsCoordinateMarginal π x i ≠ ∞ := by
  rw [gibbsCoordinateMarginal, tsum_fintype]
  exact ENNReal.sum_ne_top.2 fun σ _ ↦ π.apply_ne_top _

theorem hasPositiveGibbsCoordinateMarginals_of_apply_ne_zero
    (π : PMF (Λ → S)) (hπ : ∀ x : Λ → S, π x ≠ 0) :
    HasPositiveGibbsCoordinateMarginals π := by
  intro x i
  have hle : π x ≤ gibbsCoordinateMarginal π x i := by
    rw [gibbsCoordinateMarginal, tsum_fintype]
    simpa using
      (Finset.single_le_sum
        (fun σ _ ↦ show 0 ≤ π (gibbsCoordinateReplace x i σ) from zero_le _)
        (Finset.mem_univ (x i)) :
          π (gibbsCoordinateReplace x i (x i)) ≤ ∑ σ : S, π (gibbsCoordinateReplace x i σ))
  intro hzero
  exact hπ x (le_antisymm (hzero ▸ hle) bot_le)

/-- The single-site Gibbs transition weight from `x` to `y` obtained by updating the coordinate
`i`. It is the Gibbs ratio when `y = x^{i,y(i)}` and vanishes otherwise. -/
def gibbsCoordinateTransitionWeight (π : PMF (Λ → S)) (x : Λ → S) (i : Λ) (y : Λ → S) :
    ℝ≥0∞ :=
  let _ : DecidableEq (Λ → S) := Classical.decEq (Λ → S)
  if y = gibbsCoordinateReplace x i (y i) then
    π y / gibbsCoordinateMarginal π x i
  else
    0

/-- Definition 18.17: the Gibbs sampler transition matrix on the finite configuration space
`Λ → S`, obtained by choosing a site `i` with law `q` and resampling that coordinate according to
the textbook ratio formula `q i * π (x^{i,σ}) / π (x_{-i})`. -/
def gibbsSamplerMatrix (q : PMF Λ) (π : PMF (Λ → S)) :
    (Λ → S) → (Λ → S) → ℝ≥0∞ :=
  fun x y ↦ ∑' i : Λ, q i * gibbsCoordinateTransitionWeight π x i y

omit [Fintype S] in
/-- Evaluating the Gibbs sampler matrix gives the site-averaged single-site Gibbs weights. -/
theorem gibbsSamplerMatrix_apply
    (q : PMF Λ) (π : PMF (Λ → S)) (x y : Λ → S) :
    gibbsSamplerMatrix q π x y =
      ∑' i : Λ, q i * gibbsCoordinateTransitionWeight π x i y :=
  rfl

private def gibbsCoordinateConditional (π : PMF (Λ → S)) (x : Λ → S) (i : Λ)
    (h : gibbsCoordinateMarginal π x i ≠ 0) : PMF S :=
  PMF.normalize (fun σ ↦ π (gibbsCoordinateReplace x i σ)) h
    (gibbsCoordinateMarginal_ne_top π x i)

private theorem gibbsCoordinateConditional_apply
    (π : PMF (Λ → S)) (x : Λ → S) (i : Λ) (σ : S)
    (h : gibbsCoordinateMarginal π x i ≠ 0) :
    gibbsCoordinateConditional π x i h σ =
      π (gibbsCoordinateReplace x i σ) / gibbsCoordinateMarginal π x i := by
  simp [gibbsCoordinateConditional, gibbsCoordinateMarginal, div_eq_mul_inv]

private def gibbsCoordinateUpdatePMF (π : PMF (Λ → S)) (x : Λ → S) (i : Λ)
    (h : gibbsCoordinateMarginal π x i ≠ 0) : PMF (Λ → S) :=
  (gibbsCoordinateConditional π x i h).map (gibbsCoordinateReplace x i)

private theorem gibbsCoordinateUpdatePMF_apply
    (π : PMF (Λ → S)) (x y : Λ → S) (i : Λ)
    (h : gibbsCoordinateMarginal π x i ≠ 0) :
    gibbsCoordinateUpdatePMF π x i h y = gibbsCoordinateTransitionWeight π x i y := by
  classical
  have hmap :
      gibbsCoordinateUpdatePMF π x i h y =
        ∑ σ : S,
          if y = gibbsCoordinateReplace x i σ then
            gibbsCoordinateConditional π x i h σ
          else
            0 := by
    rw [gibbsCoordinateUpdatePMF, PMF.map, PMF.bind_apply, tsum_fintype]
    simp [PMF.pure_apply]
  rw [hmap, gibbsCoordinateTransitionWeight]
  by_cases hy : y = gibbsCoordinateReplace x i (y i)
  · rw [if_pos hy]
    rw [Finset.sum_eq_single_of_mem (y i) (Finset.mem_univ _)]
    · rw [if_pos hy]
      rw [gibbsCoordinateConditional_apply π x i (y i) h]
      have hπy : π y = π (gibbsCoordinateReplace x i (y i)) := congrArg π hy
      rw [← hπy]
    · intro σ _ hσ
      have hyσ : y ≠ gibbsCoordinateReplace x i σ := by
        intro hEq
        have hEq' : gibbsCoordinateReplace x i (y i) = gibbsCoordinateReplace x i σ :=
          hy.symm.trans hEq
        exact hσ (((gibbsCoordinateReplace_injective x i) hEq').symm)
      simp [hyσ]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro σ hσ
    have hyσ : y ≠ gibbsCoordinateReplace x i σ := by
      intro hσ'
      have hσi : y i = σ := by
        simpa using congrArg (fun z : Λ → S ↦ z i) hσ'
      exact hy (by simpa [hσi.symm] using hσ')
    simp [hyσ]

private def gibbsSamplerRow (q : PMF Λ) (π : PMF (Λ → S))
    (hπ : HasPositiveGibbsCoordinateMarginals π) (x : Λ → S) : PMF (Λ → S) :=
  q.bind fun i ↦ gibbsCoordinateUpdatePMF π x i (hπ x i)

private theorem gibbsSamplerMatrix_eq_row
    (q : PMF Λ) (π : PMF (Λ → S)) (hπ : HasPositiveGibbsCoordinateMarginals π)
    (x y : Λ → S) :
    gibbsSamplerMatrix q π x y = gibbsSamplerRow q π hπ x y := by
  simp [gibbsSamplerMatrix, gibbsSamplerRow, PMF.bind_apply, gibbsCoordinateUpdatePMF_apply]

/- The discrete kernel associated with the Gibbs sampler transition matrix. -/
abbrev gibbsSamplerKernel (q : PMF Λ) (π : PMF (Λ → S)) :
    Kernel (Λ → S) (Λ → S) :=
  discreteMatrixKernel (gibbsSamplerMatrix q π)

/-- If the single-site conditioning fibers are nonvanishing, then the Gibbs sampler transition
matrix is stochastic. -/
theorem gibbsSamplerMatrix_isStochasticMatrix
    (q : PMF Λ) (π : PMF (Λ → S)) (hπ : HasPositiveGibbsCoordinateMarginals π) :
    IsStochasticMatrix (gibbsSamplerMatrix q π) := by
  intro x
  calc
    ∑' y : Λ → S, gibbsSamplerMatrix q π x y = ∑' y : Λ → S, gibbsSamplerRow q π hπ x y := by
      refine tsum_congr fun y ↦ ?_
      simpa using gibbsSamplerMatrix_eq_row q π hπ x y
    _ = 1 := (gibbsSamplerRow q π hπ x).tsum_coe

/-- Under the nonvanishing-fiber hypothesis, the Gibbs sampler kernel is a Markov kernel. -/
theorem gibbsSamplerKernel_isMarkovKernel
    (q : PMF Λ) (π : PMF (Λ → S)) (hπ : HasPositiveGibbsCoordinateMarginals π) :
    IsMarkovKernel (gibbsSamplerKernel q π) :=
  discreteMatrixKernel_isMarkovKernel _ (gibbsSamplerMatrix_isStochasticMatrix q π hπ)

end ProbabilityTheory

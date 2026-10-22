/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_1_2

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open EuclideanSpace (single)
open scoped BigOperators EuclideanOrthant

noncomputable section

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Lemma 5.4.3.1 lies in the Chapter 5 self-concordant-barrier / recession-direction domain.

Sampled owner-style declarations in this domain:
* `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the project owner for the
  orthant `ℝ₊ⁿ`;
* `IsSelfConcordantBarrierOnWith` in `Definition_5_3_2`, the Chapter 5 owner for
  `ν`-self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions`
  in `Theorem_5_4_1_2`, the canonical owner theorem for lower bounds on the barrier parameter;
* `convex_pi` together with `convex_Ici`, the canonical mathlib convexity owner for coordinatewise
  orthant constraints.

Source/core/bridge triage:
* source-facing: the orthant specialization `ν ≥ n`;
* core/canonical: the general recession-direction owner theorem for
  `IsSelfConcordantBarrierOnWith`;
* bridge/view: the standard-basis recession directions of `ℝ₊ⁿ` and the coordinatewise orthant
  facts used to instantiate the owner theorem.

Primitive data:
* the orthant owner `nonnegativeOrthant n`;
* the barrier owner instance on `interior (nonnegativeOrthant n)`;
* the base point `(1, …, 1)` and the standard basis directions.

Derived API:
* the lower bound `(n : ℝ) ≤ (ν : ℝ)`, obtained by specializing the owner theorem with
  `αᵢ = βᵢ = 1`.

This file is therefore a source-facing specialization of the Chapter 5 owner theorem, not a
second owner abstraction. The refinement removes the isolated local proof sketch surface and
states the lemma directly as a canonical specialization of the existing owner theorem. -/

-- Proof sketch: apply
-- `barrierParameter_ge_sum_alpha_div_beta_of_recession_directions` to the convex set
-- `nonnegativeOrthant n`, with base point `xBar = (1, …, 1)`, recession directions the standard
-- basis vectors `eᵢ`, and coefficients `αᵢ = βᵢ = 1`. Then `xBar - ∑ i, αᵢ • eᵢ = 0` belongs to
-- the orthant, each backward step `xBar - eᵢ` lies on the boundary, and the left-hand side
-- becomes `∑ i, 1 = n`.
/-- Lemma 5.4.3.1: every `ν`-self-concordant barrier for the nonnegative orthant `ℝ₊ⁿ` has
barrier parameter at least `n`. -/
theorem nonnegativeOrthant_barrierParameter_ge_dimension
    {ν : NNReal} {F : Eₙ → ℝ}
    (hF : IsSelfConcordantBarrierOnWith (ℝ₊₊^n : Set Eₙ) ν F) :
    (n : ℝ) ≤ (ν : ℝ) := by
  let xBar : Eₙ := ∑ i : Fin n, single i (1 : ℝ)
  let p : Fin n → Eₙ := fun i ↦ single i (1 : ℝ)
  let e : Eₙ ≃ₜ (Fin n → ℝ) :=
    (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  have hnonnegativeOrthant :
      (ℝ₊^n : Set Eₙ) =
        e ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ici (0 : ℝ)) := by
    ext x
    simp [Pi.le_def, e, EuclideanSpace.nonnegativeOrthant]
  have hpositiveOrthant :
      (ℝ₊₊^n : Set Eₙ) =
        e ⁻¹' Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ)) := by
    ext x
    simp [e, EuclideanSpace.positiveOrthant]
  have hinterior : interior (ℝ₊^n : Set Eₙ) = (ℝ₊₊^n : Set Eₙ) := by
    rw [hnonnegativeOrthant, ← e.preimage_interior, interior_pi_set Set.finite_univ,
      hpositiveOrthant]
    simp
  have hF' : IsSelfConcordantBarrierOnWith (interior (ℝ₊^n : Set Eₙ)) ν F := by
    simpa [hinterior] using hF
  have hQ_convex : Convex ℝ (ℝ₊^n : Set Eₙ) := by
    rw [hnonnegativeOrthant]
    exact (convex_pi fun _ _ ↦ convex_Ici (0 : ℝ)).linear_preimage
      (EuclideanSpace.equiv (Fin n) ℝ).toLinearMap
  have hxBar : xBar ∈ interior (ℝ₊^n : Set Eₙ) := by
    rw [hinterior]
    simp [xBar, EuclideanSpace.mem_positiveOrthant_iff]
  have hp :
      ∀ i : Fin n,
        ∀ ⦃x : Eₙ⦄, x ∈ (ℝ₊^n : Set Eₙ) → ∀ t : ℝ, 0 ≤ t → x + t • p i ∈ (ℝ₊^n : Set Eₙ) := by
    intro i x hx t ht
    have hx' : ∀ j : Fin n, 0 ≤ x j := by
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hx
    rw [EuclideanSpace.mem_nonnegativeOrthant_iff]
    intro j
    by_cases hji : j = i
    · subst j
      simpa [p, single] using add_nonneg (hx' i) ht
    · simpa [p, single, hji] using hx' j
  have hβ_pos : ∀ i : Fin n, 0 < (1 : ℝ) := by
    intro i
    norm_num
  have hβ_exit : ∀ i : Fin n, xBar - (1 : ℝ) • p i ∉ interior (ℝ₊^n : Set Eₙ) := by
    intro i
    rw [hinterior, EuclideanSpace.mem_positiveOrthant_iff]
    intro hx
    have hxi := hx i
    simp [xBar, p, single] at hxi
  have hα_nonneg : ∀ i : Fin n, 0 ≤ (1 : ℝ) := by
    intro i
    norm_num
  have hy : xBar - ∑ i, (1 : ℝ) • p i ∈ (ℝ₊^n : Set Eₙ) := by
    simp [EuclideanSpace.mem_nonnegativeOrthant_iff, p, xBar, single]
  have hbound : ∑ i : Fin n, (1 : ℝ) / 1 ≤ (ν : ℝ) :=
    hF'.barrierParameter_ge_sum_alpha_div_beta_of_recession_directions
      hQ_convex hxBar p
      hp
      (fun _ : Fin n ↦ (1 : ℝ)) (fun _ : Fin n ↦ (1 : ℝ))
      hβ_pos hβ_exit hα_nonneg hy
  simpa [xBar, p] using hbound

end

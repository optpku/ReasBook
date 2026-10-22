/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 7.40 lies in Chapter 7's relative-scale / scalar iteration-bound domain.

Relevant owner-style declarations sampled before refinement:
- `mixedAccuracyIterationCountBound` in `Proposition_7_38`, the sibling Chapter 7 owner for the
  logarithmic iteration budget in the same quasi-Newton complexity lane;
- `mixedAccuracyUniformIterationCountBound` in `Proposition_7_38`, the companion dimension-free
  comparison owner for that sibling bound;
- `mixedAccuracyIterationCountBound_lt_uniformUpperBound` in `Proposition_7_38`, the matching
  strict comparison theorem whose proof has the same `log (1 + x) < x` structure;
- `quasiNewton_bestPoint_relative_accuracy_of_iterationBound` in `Proposition_7_39`, the direct
  downstream theorem that uses the present logarithmic budget as a sufficient lower bound on the
  iteration index.

Best owner abstraction:
- source-facing: the textbook relative-scale iteration budget `R_n(δ)`;
- core/canonical: the scalar owner `relativeScaleIterationBound`;
- bridge/view: the expansion theorem `relativeScaleIterationBound_def` and the dimension-free
  comparison owner `relativeScaleUniformIterationBound`.

Primitive data:
- the positive dimension `n : ℕ+`;
- the constants `δ`, `L`, `R`, and `fStar`.

Derived API:
- the logarithmic expansion of `R_n(δ)`;
- the dimension-free comparison quantity `R_∞(δ)`;
- the strict comparison theorem between the finite-dimensional and dimension-free bounds.

The earlier version left the owner-level expansion theorems and strict comparison theorem as
unstructured placeholders, while the direct downstream theorem in `Proposition_7_39` repeated the
raw logarithmic formula instead of using the owner introduced here. This refinement keeps the same
mathematical semantics, proves the definitional bridge theorems directly, and makes the owner file
the canonical surface for the relative-scale budget.
-/

/-- The relative-scale iteration bound `R_n(δ)` from `(7.4.24)` in dimension `n`. -/
abbrev relativeScaleIterationBound
    (n : ℕ+) (δ L R fStar : ℝ) : ℝ :=
  ((n : ℝ) / δ) *
    Real.log
      (1 +
        ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
          (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ))

-- Proof sketch: unfold `relativeScaleIterationBound`.
/-- Expanding `relativeScaleIterationBound n δ L R fStar` recovers the logarithmic formula from
`(7.4.24)`. -/
theorem relativeScaleIterationBound_def
    (n : ℕ+) (δ L R fStar : ℝ) :
    relativeScaleIterationBound n δ L R fStar =
      ((n : ℝ) / δ) *
        Real.log
          (1 +
            ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
              (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ)) := rfl

/-- The dimension-free bound `R_∞(δ) = L² R² / (δ² (1 - 2δ) (f^*)²)` for the relative-scale
iteration complexity. -/
abbrev relativeScaleUniformIterationBound
    (δ L R fStar : ℝ) : ℝ :=
  (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
    (δ ^ (2 : ℕ) * (1 - 2 * δ) * fStar ^ (2 : ℕ))

-- Proof sketch: unfold `relativeScaleUniformIterationBound`.
/-- Expanding `relativeScaleUniformIterationBound δ L R fStar` recovers the formula
`L² R² / (δ² (1 - 2δ) (f^*)²)`. -/
theorem relativeScaleUniformIterationBound_def
    (δ L R fStar : ℝ) :
    relativeScaleUniformIterationBound δ L R fStar =
      (L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
        (δ ^ (2 : ℕ) * (1 - 2 * δ) * fStar ^ (2 : ℕ)) := rfl

-- Proof sketch: write `relativeScaleIterationBound n δ L R fStar` as
-- `(1 / δ) * ((n : ℝ) * log (1 + C / n))` with
-- `C = L² R² / (δ (1 - 2δ) (f^*)²) > 0`. Then use `log (1 + x) < x` for `x > 0` to obtain
-- `(n : ℝ) * log (1 + C / n) < C`, and simplify the right-hand side to
-- `L² R² / (δ² (1 - 2δ) (f^*)²)`.
/-- Proposition 7.40: if `δ ∈ (0, 1 / 2)` and the relative-scale constants `L`, `R`, and `f^*`
are positive, then the iteration bound `R_n(δ)` from `(7.4.24)` is strictly less than the
dimension-free quantity `R_∞(δ) = L² R² / (δ² (1 - 2δ) (f^*)²)`. -/
theorem relativeScaleIterationBound_lt_uniformBound
    (n : ℕ+) (δ L R fStar : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2))
    (hL : 0 < L) (hR : 0 < R) (hfStar : 0 < fStar) :
    relativeScaleIterationBound n δ L R fStar <
      relativeScaleUniformIterationBound δ L R fStar := by
  let x : ℝ :=
    ((L ^ (2 : ℕ) * R ^ (2 : ℕ)) /
      (δ * (1 - 2 * δ) * fStar ^ (2 : ℕ))) / (n : ℝ)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast n.2
  have h_one_sub_twoδ : 0 < 1 - 2 * δ := by
    nlinarith [hδ.2]
  have hx : 0 < x := by
    dsimp [x]
    have hnum : 0 < L ^ (2 : ℕ) * R ^ (2 : ℕ) := by
      positivity
    have hden : 0 < δ * (1 - 2 * δ) * fStar ^ (2 : ℕ) := by
      have hfStar_sq : 0 < fStar ^ (2 : ℕ) := by
        positivity
      exact mul_pos (mul_pos hδ.1 h_one_sub_twoδ) hfStar_sq
    exact div_pos (div_pos hnum hden) hn
  have hlog : Real.log (1 + x) < x := by
    have hpos : 0 < 1 + x := by linarith
    have hne : 1 + x ≠ (1 : ℝ) := by linarith
    simpa [sub_eq_add_neg] using Real.log_lt_sub_one_of_pos hpos hne
  have hmul :
      (n : ℝ) / δ * Real.log (1 + x) <
        (n : ℝ) / δ * x := by
    exact mul_lt_mul_of_pos_left hlog (div_pos hn hδ.1)
  have hδ_ne : δ ≠ 0 := hδ.1.ne'
  have hn_ne : (n : ℝ) ≠ 0 := hn.ne'
  have h_one_sub_twoδ_ne : 1 - 2 * δ ≠ 0 := h_one_sub_twoδ.ne'
  have hfStar_sq_ne : fStar ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hfStar.ne'
  calc
    relativeScaleIterationBound n δ L R fStar
        = (n : ℝ) / δ * Real.log (1 + x) := by
          simp [relativeScaleIterationBound, x]
    _ < (n : ℝ) / δ * x := hmul
    _ = relativeScaleUniformIterationBound δ L R fStar := by
          dsimp [relativeScaleUniformIterationBound, x]
          field_simp [hδ_ne, hn_ne, h_one_sub_twoδ_ne, hfStar_sq_ne]

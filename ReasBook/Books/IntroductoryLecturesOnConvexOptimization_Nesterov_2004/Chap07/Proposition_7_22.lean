/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace
open scoped Pointwise

universe u

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n

/- Proposition 7.22 lies in Chapter 7's symmetric-matrix spectral-radius minimization domain.

Sampled owner-style declarations:
- `ρ(X)` in `Definition_7_17`, the chapter owner for the real-valued spectral radius on `𝕊^n`;
- `𝕊^n` in Chapter 5, the chapter owner for real symmetric matrices;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the project's
  canonical optimization-value owner for a feasible set and real-valued objective;
- `SpectralRadiusMinimizationProblem.maxRank` in `Definition_7_45`, the later chapter owner for
  `sup_y rank(A y)` in the specialized optimization problem.

Best owner abstraction:
- source-facing: Proposition 7.22's induced lower and upper bounds for `f_p*` along an arbitrary
  family `A : Q → 𝕊^n`;
- core/canonical: the chapter owners `𝕊^n` and `ρ(X)`, together with the Chapter 1 constrained
  minimization owner for the induced infima and `sSup` for the rank bound;
- bridge/view: the named source quantities `inducedRadiusInf`, `inducedRankSup`, and
  `inducedObjectiveInf`.

Primitive data:
- a feasible type `Q`;
- a family `A : Q → 𝕊^n`;
- an exponent parameter `p : ℕ+`;
- the objective `F_p : 𝕊^n → ℝ`;
- the pointwise lower and upper bounds on `F_p`.

Derived API:
- `φ*` as the canonical owner optimal value of `y ↦ ρ(A y)`;
- `r = sup_y rank(A y)`;
- `f_p*` as the canonical owner optimal value of `y ↦ F_p(A y)`.

Source/core/bridge triage:
- source-facing: the proposition below and the three named source quantities `φ*`, `r`, `f_p*`;
- core/canonical: `ρ(X)` on `𝕊^n`, `SetConstrainedMinimizationProblem.optimalValue`, and `sSup`;
- bridge/view: the explicit `EReal`-infimum formulas and the final real-valued inequality bridge.

The previous file duplicated the chapter symmetric-matrix carrier with a local subtype
`selfAdjoint (Matrix ...)`, treated the spectral radius as an arbitrary parameter `ρ`, and
totalized the source infima as plain real `sInf` values on an arbitrary type `Q`. This refinement
keeps the source-facing quantities `φ*`, `r`, and `f_p*`, but moves the two infima onto the
canonical Chapter 1 optimal-value owner so empty families no longer silently collapse to `0`. The
proposition itself is then the finite real-surface bridge for those canonical optimal values.
-/

/-- The infimum `φ*` of the spectral radii `ρ(A y)` along a family of symmetric matrices, encoded
as the canonical constrained optimal value on the feasible type `Q`. -/
def inducedRadiusInf {Q : Type u} (A : Q → SymmMat) : EReal :=
  (.mk Set.univ fun y : Q ↦ ρ(A y) : SetConstrainedMinimizationProblem Q).optimalValue

/-- Expanding `inducedRadiusInf` recovers the extended-real infimum of `ρ(A y)` over `Q`. -/
theorem inducedRadiusInf_eq_sInf_range {Q : Type u} (A : Q → SymmMat) :
    inducedRadiusInf A = sInf (Set.range fun y : Q ↦ (ρ(A y) : EReal)) := by
  let problem : SetConstrainedMinimizationProblem Q := .mk Set.univ fun y ↦ ρ(A y)
  simpa [inducedRadiusInf, problem, Set.image_univ] using problem.optimalValue_eq_sInf_image

/-- The supremum `r` of the ranks of the symmetric matrices `A y`. -/
def inducedRankSup {Q : Type u} (A : Q → SymmMat) : ℕ :=
  sSup (Set.range fun y : Q ↦ Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ))

/-- The induced objective infimum `f_p*`, encoded as the canonical constrained optimal value of
`y ↦ F_p(A y)` on the feasible type `Q`. -/
def inducedObjectiveInf {Q : Type u} (F_p : SymmMat → ℝ) (A : Q → SymmMat) : EReal :=
  (.mk Set.univ fun y : Q ↦ F_p (A y) : SetConstrainedMinimizationProblem Q).optimalValue

/-- Expanding `inducedObjectiveInf` recovers the extended-real infimum of `F_p(A y)` over `Q`. -/
theorem inducedObjectiveInf_eq_sInf_range {Q : Type u} (F_p : SymmMat → ℝ) (A : Q → SymmMat) :
    inducedObjectiveInf F_p A = sInf (Set.range fun y : Q ↦ (F_p (A y) : EReal)) := by
  let problem : SetConstrainedMinimizationProblem Q := .mk Set.univ fun y ↦ F_p (A y)
  simpa [inducedObjectiveInf, problem, Set.image_univ] using
    problem.optimalValue_eq_sInf_image

/-- Helper for Proposition 7.22: on a nonempty feasible type, the Chapter 1 owner optimal value
for a real-valued objective agrees with the real infimum of its range, viewed in `EReal`. -/
private theorem optimalValue_eq_coe_sInf_range_of_nonempty_bddBelow
    {Q : Type u} [Nonempty Q] (g : Q → ℝ) (hbounded : BddBelow (Set.range g)) :
    (.mk Set.univ g : SetConstrainedMinimizationProblem Q).optimalValue =
      ((sInf (Set.range g) : ℝ) : EReal) := by
  -- Transport the real greatest-lower-bound characterization across the coercion `ℝ → EReal`.
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  have hs :
      IsGLB (Set.range fun x : Q ↦ (g x : EReal)) (((sInf (Set.range g) : ℝ) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact EReal.coe_le_coe (csInf_le hbounded ⟨y, rfl⟩)
    · intro z hz
      by_cases hz_bot : z = ⊥
      · simp [hz_bot]
      · have hz_top : z ≠ ⊤ := by
          intro hz_eq_top
          obtain ⟨x⟩ := ‹Nonempty Q›
          have hz_mem : z ≤ (g x : EReal) := hz ⟨x, rfl⟩
          simp [hz_eq_top] at hz_mem
        lift z to ℝ using ⟨hz_top, hz_bot⟩ with r
        have hr : r ≤ sInf (Set.range g) := by
          refine le_csInf ?_ ?_
          · obtain ⟨x⟩ := ‹Nonempty Q›
            exact ⟨g x, ⟨x, rfl⟩⟩
          · intro y hy
            rcases hy with ⟨x, rfl⟩
            have hzy : (r : EReal) ≤ (g x : EReal) := hz ⟨x, rfl⟩
            exact_mod_cast hzy
        exact_mod_cast hr
  have hs' : (Set.range fun x : Q ↦ (g x : EReal)).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty Q›
    exact ⟨g x, ⟨x, rfl⟩⟩
  simpa [Set.image_univ] using hs.csInf_eq hs'

/-- Helper for Proposition 7.22: under nonemptiness and a lower bound on the range, the owner
optimal value projects back to the textbook real infimum via `.toReal`. -/
private theorem optimalValue_toReal_eq_sInf_range_of_nonempty_bddBelow
    {Q : Type u} [Nonempty Q] (g : Q → ℝ) (hbounded : BddBelow (Set.range g)) :
    ((.mk Set.univ g : SetConstrainedMinimizationProblem Q).optimalValue).toReal =
      sInf (Set.range g) := by
  -- First identify the owner value with a finite `EReal`, then remove the coercion.
  rw [optimalValue_eq_coe_sInf_range_of_nonempty_bddBelow g hbounded]
  simp

/-- Helper for Proposition 7.22: on a nonnegative range, squaring commutes with taking the
infimum. -/
private theorem sInf_sq_range_eq_sq_sInf_range_of_nonneg
    {Q : Type u} [Nonempty Q] (φ : Q → ℝ) (hφ_nonneg : ∀ y, 0 ≤ φ y) :
    sInf (Set.range fun y ↦ φ y ^ (2 : ℕ)) = (sInf (Set.range φ)) ^ (2 : ℕ) := by
  let A : Set ℝ := Set.range φ
  have hA_nonempty : A.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty Q›
    exact ⟨φ x, ⟨x, rfl⟩⟩
  have hA_bddBelow : BddBelow A := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hφ_nonneg y
  have hA_subset : A ⊆ Set.Ici 0 := by
    rintro _ ⟨y, rfl⟩
    exact hφ_nonneg y
  have hmono : MonotoneOn (fun x : ℝ ↦ x * x) A := by
    exact (strictMonoOn_mul_self.monotoneOn).mono hA_subset
  have hsq :
      (sInf A) * sInf A = sInf ((fun x : ℝ ↦ x * x) '' A) := by
    -- The square map is continuous and monotone on the nonnegative feasible image.
    simpa [pow_two] using
      (MonotoneOn.map_csInf_of_continuousWithinAt
        (A := A) (f := fun x : ℝ ↦ x * x)
        (continuous_id.mul continuous_id).continuousWithinAt
        hmono hA_nonempty hA_bddBelow)
  have himage :
      ((fun x : ℝ ↦ x * x) '' A) = Set.range fun y ↦ φ y ^ (2 : ℕ) := by
    ext z
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, by simp [pow_two]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨φ y, ⟨y, rfl⟩, by simp [pow_two]⟩
  -- Rewrite the square-image infimum back to the original range.
  simpa [A, himage, pow_two] using hsq.symm

/-- Helper for Proposition 7.22: for a nonnegative range and nonnegative scalar, scaling also
commutes with taking the infimum of the quadratic model. -/
private theorem sInf_scaled_sq_range_eq_of_nonneg
    {Q : Type u} [Nonempty Q] (φ : Q → ℝ) {c : ℝ} (hc_nonneg : 0 ≤ c)
    (hφ_nonneg : ∀ y, 0 ≤ φ y) :
    sInf (Set.range fun y ↦ c * φ y ^ (2 : ℕ)) = c * (sInf (Set.range φ)) ^ (2 : ℕ) := by
  have himage :
      Set.range (fun y ↦ c * φ y ^ (2 : ℕ)) = c • Set.range (fun y ↦ φ y ^ (2 : ℕ)) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨φ y ^ (2 : ℕ), ⟨y, rfl⟩, by simp [smul_eq_mul]⟩
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, by simp [smul_eq_mul]⟩
  calc
    sInf (Set.range fun y ↦ c * φ y ^ (2 : ℕ))
        = sInf (c • Set.range fun y ↦ φ y ^ (2 : ℕ)) := by rw [himage]
    _ = c • sInf (Set.range fun y ↦ φ y ^ (2 : ℕ)) := by
      simpa using Real.sInf_smul_of_nonneg hc_nonneg (Set.range fun y ↦ φ y ^ (2 : ℕ))
    _ = c * sInf (Set.range fun y ↦ φ y ^ (2 : ℕ)) := by simp [smul_eq_mul]
    _ = c * (sInf (Set.range φ)) ^ (2 : ℕ) := by
      rw [sInf_sq_range_eq_sq_sInf_range_of_nonneg φ hφ_nonneg]

/-- Helper for Proposition 7.22: the pointwise rank term is uniformly bounded by the global
supremum `inducedRankSup A`, so the same holds after applying the exponent `1 / p`. -/
private theorem rank_rpow_le_inducedRankSup_rpow
    {Q : Type u} [Nonempty Q] (A : Q → SymmMat) (p : ℕ+) (y : Q) :
    ((Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ) : ℝ) ^ (1 / (p : ℝ))) ≤
      ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) := by
  have hrank_bdd :
      BddAbove (Set.range fun z : Q ↦ Matrix.rank (A z : Matrix (Fin n) (Fin n) ℝ)) := by
    refine ⟨n, ?_⟩
    rintro _ ⟨z, rfl⟩
    exact Matrix.rank_le_width _
  have hrank_le :
      Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ) ≤ inducedRankSup A := by
    simpa [inducedRankSup] using
      (le_csSup hrank_bdd (Set.mem_range_self y))
  exact Real.rpow_le_rpow
    (by exact_mod_cast (Nat.zero_le (Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ))))
    (by exact_mod_cast hrank_le)
    (by positivity)

-- Proof sketch: because `Q` is nonempty, the two owner optimal values are finite and their
-- `toReal` projections recover the textbook real infima. Apply the assumed pointwise inequalities
-- to `A y`; the lower bound follows by taking infima of `(1 / 2) * ρ(A y)^2 ≤ F_p(A y)`, and the
-- upper bound uses `Matrix.rank (A y) ≤ inducedRankSup A` before taking infima.
/-- Proposition 7.22: if `F_p` satisfies the pointwise bounds
`(1 / 2) ρ(X)^2 ≤ F_p(X) ≤ (1 / 2) ρ(X)^2 (rank X)^(1 / p)` on real symmetric matrices, then the
induced infimum `f_p* = inf_y F_p(A y)`, read as the real part of the canonical owner optimal
value on a nonempty feasible type `Q`, satisfies
`(1 / 2) φ*^2 ≤ f_p* ≤ (1 / 2) φ*^2 r^(1 / p)`, where
`φ* = inf_y ρ(A y)` is read in the same way and `r = sup_y rank(A y)`. -/
theorem inducedObjectiveInf_bounds
    {Q : Type u} [Nonempty Q] (p : ℕ+) (F_p : SymmMat → ℝ) (A : Q → SymmMat)
    (h_lower : ∀ X, (1 / 2 : ℝ) * ρ(X) ^ (2 : ℕ) ≤ F_p X)
    (h_upper : ∀ X,
      F_p X ≤ (1 / 2 : ℝ) * ρ(X) ^ (2 : ℕ) *
        ((Matrix.rank (X : Matrix (Fin n) (Fin n) ℝ) : ℝ) ^ (1 / (p : ℝ)))) :
    (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) ≤
        (inducedObjectiveInf F_p A).toReal ∧
      (inducedObjectiveInf F_p A).toReal ≤
        (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) *
          ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) :=
by
  let φ : Q → ℝ := fun y ↦ ρ(A y)
  let fp : Q → ℝ := fun y ↦ F_p (A y)
  let lowerModel : Q → ℝ := fun y ↦ (1 / 2 : ℝ) * φ y ^ (2 : ℕ)
  let upperCoeff : ℝ := (1 / 2 : ℝ) * ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ)))
  let upperModel : Q → ℝ := fun y ↦ upperCoeff * φ y ^ (2 : ℕ)
  let lowerProblem : SetConstrainedMinimizationProblem Q := .mk Set.univ lowerModel
  let fpProblem : SetConstrainedMinimizationProblem Q := .mk Set.univ fp
  let upperProblem : SetConstrainedMinimizationProblem Q := .mk Set.univ upperModel
  have hφ_nonneg : ∀ y, 0 ≤ φ y := by
    -- The spectral radius is a nonnegative real-valued quantity.
    intro y
    dsimp [φ]
    positivity
  have hφ_bddBelow : BddBelow (Set.range φ) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact hφ_nonneg y
  have hlowerModel_bddBelow : BddBelow (Set.range lowerModel) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp [lowerModel]
    positivity
  have hupperCoeff_nonneg : 0 ≤ upperCoeff := by
    -- The uniform rank factor and the prefactor `1 / 2` are both nonnegative.
    dsimp [upperCoeff]
    positivity
  have hupperModel_bddBelow : BddBelow (Set.range upperModel) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    dsimp [upperModel]
    positivity
  have hfp_bddBelow : BddBelow (Set.range fp) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨y, rfl⟩
    have hlower_nonneg : 0 ≤ (1 / 2 : ℝ) * φ y ^ (2 : ℕ) := by
      positivity
    exact hlower_nonneg.trans (by simpa [fp, φ] using h_lower (A y))
  have hradius_toReal : (inducedRadiusInf A).toReal = sInf (Set.range φ) := by
    -- Rewrite the owner optimal value back to the textbook infimum of the radii.
    simpa [inducedRadiusInf, φ] using
      (optimalValue_toReal_eq_sInf_range_of_nonempty_bddBelow (g := φ) hφ_bddBelow)
  have hfp_toReal : (inducedObjectiveInf F_p A).toReal = sInf (Set.range fp) := by
    -- The induced objective infimum has the same owner-to-infimum description.
    simpa [inducedObjectiveInf, fp] using
      (optimalValue_toReal_eq_sInf_range_of_nonempty_bddBelow (g := fp) hfp_bddBelow)
  have hfpProblem_toReal : fpProblem.optimalValue.toReal = (inducedObjectiveInf F_p A).toReal := by
    -- The owner problem `fpProblem` is definitionally the same induced objective owner.
    simp [fpProblem, inducedObjectiveInf, fp]
  have hlowerProblem_toReal :
      lowerProblem.optimalValue.toReal =
        (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) := by
    -- Evaluate the lower quadratic model exactly at the infimum radius.
    calc
      lowerProblem.optimalValue.toReal = sInf (Set.range lowerModel) := by
        exact optimalValue_toReal_eq_sInf_range_of_nonempty_bddBelow
          (g := lowerModel) hlowerModel_bddBelow
      _ = (1 / 2 : ℝ) * (sInf (Set.range φ)) ^ (2 : ℕ) := by
        rw [sInf_scaled_sq_range_eq_of_nonneg (φ := φ) (c := (1 / 2 : ℝ)) (by positivity)
          hφ_nonneg]
      _ = (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) := by
        rw [← hradius_toReal]
  have hupperProblem_toReal :
      upperProblem.optimalValue.toReal =
        (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) *
          ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) := by
    -- Evaluate the uniform upper model by pulling the global rank factor through the infimum.
    calc
      upperProblem.optimalValue.toReal = sInf (Set.range upperModel) := by
        exact optimalValue_toReal_eq_sInf_range_of_nonempty_bddBelow
          (g := upperModel) hupperModel_bddBelow
      _ = upperCoeff * (sInf (Set.range φ)) ^ (2 : ℕ) := by
        rw [sInf_scaled_sq_range_eq_of_nonneg (φ := φ) (c := upperCoeff) hupperCoeff_nonneg
          hφ_nonneg]
      _ = upperCoeff * (inducedRadiusInf A).toReal ^ (2 : ℕ) := by
        rw [← hradius_toReal]
      _ = (1 / 2 : ℝ) * (inducedRadiusInf A).toReal ^ (2 : ℕ) *
            ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) := by
        dsimp [upperCoeff]
        ring
  have hlowerProblem_ne_bot : lowerProblem.optimalValue ≠ ⊥ := by
    rw [optimalValue_eq_coe_sInf_range_of_nonempty_bddBelow (g := lowerModel) hlowerModel_bddBelow]
    exact EReal.coe_ne_bot _
  have hfpProblem_ne_bot : fpProblem.optimalValue ≠ ⊥ := by
    rw [optimalValue_eq_coe_sInf_range_of_nonempty_bddBelow (g := fp) hfp_bddBelow]
    exact EReal.coe_ne_bot _
  have hfpProblem_ne_top : fpProblem.optimalValue ≠ ⊤ := by
    rw [optimalValue_eq_coe_sInf_range_of_nonempty_bddBelow (g := fp) hfp_bddBelow]
    exact EReal.coe_ne_top _
  have hupperProblem_ne_top : upperProblem.optimalValue ≠ ⊤ := by
    rw [optimalValue_eq_coe_sInf_range_of_nonempty_bddBelow (g := upperModel) hupperModel_bddBelow]
    exact EReal.coe_ne_top _
  have h_lower_opt :
      lowerProblem.optimalValue ≤ fpProblem.optimalValue := by
    -- Compare the lower quadratic model with the induced objective pointwise and pass to owners.
    refine SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      lowerProblem fpProblem rfl ?_
    intro y _
    simpa [lowerProblem, fpProblem, lowerModel, fp, φ] using h_lower (A y)
  have h_upper_opt :
      fpProblem.optimalValue ≤ upperProblem.optimalValue := by
    -- Route correction: bound the pointwise rank term by the global supremum before taking infima.
    refine SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
      fpProblem upperProblem rfl ?_
    intro y _
    have hrank :
        ((Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ) : ℝ) ^ (1 / (p : ℝ))) ≤
          ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) :=
      rank_rpow_le_inducedRankSup_rpow A p y
    have hfactor_nonneg : 0 ≤ (1 / 2 : ℝ) * φ y ^ (2 : ℕ) := by
      positivity
    calc
      fp y ≤
          (1 / 2 : ℝ) * φ y ^ (2 : ℕ) *
            ((Matrix.rank (A y : Matrix (Fin n) (Fin n) ℝ) : ℝ) ^ (1 / (p : ℝ))) := by
        simpa [fp, φ] using h_upper (A y)
      _ ≤ (1 / 2 : ℝ) * φ y ^ (2 : ℕ) *
            ((inducedRankSup A : ℝ) ^ (1 / (p : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hrank hfactor_nonneg
      _ = upperModel y := by
        dsimp [upperModel, upperCoeff]
        ring
  constructor
  · -- Rewrite both owner optimal values to their real infimum forms and compare them.
    have hLowerReal : lowerProblem.optimalValue.toReal ≤ fpProblem.optimalValue.toReal := by
      exact EReal.toReal_le_toReal h_lower_opt hlowerProblem_ne_bot hfpProblem_ne_top
    rw [hlowerProblem_toReal, hfpProblem_toReal] at hLowerReal
    exact hLowerReal
  · -- The same owner comparison yields the upper sandwich after evaluating the upper model.
    have hUpperReal : fpProblem.optimalValue.toReal ≤ upperProblem.optimalValue.toReal := by
      exact EReal.toReal_le_toReal h_upper_opt hfpProblem_ne_bot hupperProblem_ne_top
    rw [hfpProblem_toReal, hupperProblem_toReal] at hUpperReal
    exact hUpperReal

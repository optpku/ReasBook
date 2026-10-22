/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_5_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_5_5

open Matrix

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced `Matrix.PosDef` and
-- `Matrix.IsHermitian.posDef_iff_eigenvalues_pos` as the canonical positivity-facing matrix API,
-- while nearby repository precedent still expresses the SSVM condition number by the ratio of
-- ordered representative eigenvalues. This item therefore keeps the source-facing SSVM
-- representative matrix surface but places `κ` on a positive-definite owner.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The largest ordered eigenvalue `λ₁` of a positive-definite representative matrix. -/
def largestOrderedRepresentativeEigenvalue {R : MatrixN} (hRpos : R.PosDef) (hn : 0 < n) : ℝ :=
  let hR := (Matrix.posDef_iff_dotProduct_mulVec.mp hRpos).1
  hR.eigenvalues ⟨0, hn⟩

/-- The smallest ordered eigenvalue `λₙ` of a positive-definite representative matrix. -/
def smallestOrderedRepresentativeEigenvalue
    {R : MatrixN} (hRpos : R.PosDef) (hn : 0 < n) : ℝ :=
  let hR := (Matrix.posDef_iff_dotProduct_mulVec.mp hRpos).1
  hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩

/-- The spectral condition number `κ(R)` of a positive-definite representative matrix, expressed
as the ratio `λ₁ / λₙ` of its largest and smallest ordered eigenvalues. -/
def ssvmRepresentativeConditionNumber {R : MatrixN} (hRpos : R.PosDef) (hn : 0 < n) : ℝ :=
  largestOrderedRepresentativeEigenvalue hRpos hn /
    smallestOrderedRepresentativeEigenvalue hRpos hn

/-- The spectral condition number of the SSVM representative update
`ssvmInverseUpdate R r r φ γ`. -/
def ssvmUpdatedRepresentativeConditionNumber
    {R : MatrixN} (r : Point) (φ γ : ℝ)
    (hRφpos : (ssvmInverseUpdate R r r φ γ).PosDef) (hn : 0 < n) : ℝ :=
  ssvmRepresentativeConditionNumber hRφpos hn

/-- If `R` is positive definite, `φ ∈ Set.Icc (0 : ℝ) 1`, `0 < γ`, and the SSVM step is nonzero
in the sense `dotProduct r r ≠ 0`, then the specialized SSVM update
`ssvmInverseUpdate R r r φ γ` from `(5.5.24)` remains positive definite. -/
theorem ssvmInverseUpdate_self_posDef
    {R : MatrixN} (hRpos : R.PosDef) (r : Point)
    (hrr : dotProduct r r ≠ 0) {φ γ : ℝ}
    (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) :
    (ssvmInverseUpdate R r r φ γ).PosDef := by
  -- Reuse the earlier SSVM positivity theorem once the self-curvature denominator is known
  -- to be strictly positive.
  have hr_ne : r ≠ 0 := by
    intro hr
    apply hrr
    simp [hr]
  have hr_ofLp_ne : r.ofLp ≠ 0 := by
    simpa using hr_ne
  have hrr_pos : 0 < dotProduct r r := by
    simpa using (dotProduct_self_star_pos_iff (v := r.ofLp)).2 hr_ofLp_ne
  exact ssvmInverseUpdate_posDef R hRpos r r φ γ hφ.1 hγ hrr_pos

/-- Helper for Chapter05 Corollary 5.5.7: clearing the positive denominator `γ` converts the
reciprocal endpoint bounds into the scaled inequalities used by Theorem 5.5.5. -/
lemma scaledRepresentativeEndpointInequalities
    {R : MatrixN} (hRpos : R.PosDef) (hn : 0 < n) {γ : ℝ} (hγ : 0 < γ)
    (hLower : smallestOrderedRepresentativeEigenvalue hRpos hn ≤ 1 / γ)
    (hUpper : 1 / γ ≤ largestOrderedRepresentativeEigenvalue hRpos hn) :
    γ * smallestOrderedRepresentativeEigenvalue hRpos hn ≤ 1 ∧
      1 ≤ γ * largestOrderedRepresentativeEigenvalue hRpos hn := by
  constructor
  · -- Multiply the lower endpoint inequality by the positive scalar `γ`.
    have hScaled :=
      (le_div_iff₀ hγ).mp hLower
    simpa [mul_comm, mul_left_comm, mul_assoc] using hScaled
  · -- Multiply the upper endpoint inequality by the positive scalar `γ`.
    have hScaled :=
      (div_le_iff₀ hγ).mp hUpper
    simpa [mul_comm, mul_left_comm, mul_assoc] using hScaled

/-- Helper for Chapter05 Corollary 5.5.7: a finite real sequence whose first value is above `1`
and whose last value is at most `1` has a first adjacent crossing of the level `1`. -/
lemma endpointCrossingIndex
    {f : Fin n → ℝ} (hn : 0 < n)
    (hLast : f ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ ≤ 1)
    (hFirst : ¬ f ⟨0, hn⟩ ≤ 1) :
    ∃ k : ℕ, ∃ hk : k + 1 < n, f ⟨k + 1, hk⟩ ≤ 1 ∧
      1 ≤ f ⟨k, Nat.lt_of_succ_lt hk⟩ := by
  let P : ℕ → Prop := fun m => ∃ hm : m < n, f ⟨m, hm⟩ ≤ 1
  have hExists : ∃ m : ℕ, P m := by
    refine ⟨n - 1, ?_⟩
    exact ⟨Nat.sub_lt hn (Nat.succ_pos 0), hLast⟩
  let m := Nat.find hExists
  have hmSpec : P m := Nat.find_spec hExists
  rcases hmSpec with ⟨hm_lt, hm_le⟩
  have hm_pos : 0 < m := by
    -- The first qualifying index cannot be `0`, because the initial value is strictly above `1`.
    by_contra hm_not_pos
    have hm_zero : m = 0 := Nat.eq_zero_of_not_pos hm_not_pos
    have hm_lt_zero : 0 < n := by
      simpa [hm_zero] using hm_lt
    have hm_le_zero : f ⟨0, hm_lt_zero⟩ ≤ 1 := by
      simpa [hm_zero] using hm_le
    have hm_index_eq : (⟨0, hm_lt_zero⟩ : Fin n) = ⟨0, hn⟩ := by
      ext
      rfl
    apply hFirst
    simpa [hm_index_eq] using hm_le_zero
  have hk : (m - 1) + 1 < n := by
    -- The predecessor index still lies one step before the first crossing.
    have hm_eq : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    simpa [hm_eq] using hm_lt
  refine ⟨m - 1, hk, ?_, ?_⟩
  · -- By construction, the first qualifying index already lies at or below the level `1`.
    have hm_eq : (m - 1) + 1 = m := Nat.sub_add_cancel (Nat.succ_le_of_lt hm_pos)
    simpa [hm_eq] using hm_le
  · -- Minimality of `m` forces the predecessor value to stay above `1`.
    have hPrevLt : m - 1 < n := by
      exact lt_of_lt_of_le
        (Nat.sub_lt (Nat.succ_le_of_lt hm_pos) (Nat.succ_pos 0))
        hm_lt.le
    have hPrevNotLe : ¬ f ⟨m - 1, hPrevLt⟩ ≤ 1 := by
      intro hPrevLe
      have hFindLe : m ≤ m - 1 :=
        Nat.find_min' hExists ⟨hPrevLt, hPrevLe⟩
      have hPrevLtSelf : m - 1 < m :=
        Nat.sub_lt (Nat.succ_le_of_lt hm_pos) (Nat.succ_pos 0)
      exact (Nat.not_le_of_gt hPrevLtSelf) hFindLe
    exact le_of_lt (lt_of_not_ge hPrevNotLe)

/-- Helper for Chapter05 Corollary 5.5.7: the ordered endpoints of the SSVM update lie between
the scaled ordered endpoints of the original representative matrix. -/
lemma ssvmUpdatedOrderedEndpointBounds
    {R : MatrixN} (hRpos : R.PosDef) (r : Point)
    (hrr : dotProduct r r ≠ 0) {φ γ : ℝ}
    (hn : 0 < n) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hLower : smallestOrderedRepresentativeEigenvalue hRpos hn ≤ 1 / γ)
    (hUpper : 1 / γ ≤ largestOrderedRepresentativeEigenvalue hRpos hn) :
    γ * smallestOrderedRepresentativeEigenvalue hRpos hn ≤
        (ssvmInverseUpdate_self_isHermitian hRpos.isHermitian r φ γ).eigenvalues
          ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ ∧
      (ssvmInverseUpdate_self_isHermitian hRpos.isHermitian r φ γ).eigenvalues ⟨0, hn⟩ ≤
        γ * largestOrderedRepresentativeEigenvalue hRpos hn := by
  let hR : R.IsHermitian := hRpos.isHermitian
  let hRφ : (ssvmInverseUpdate R r r φ γ).IsHermitian :=
    ssvmInverseUpdate_self_isHermitian hRpos.isHermitian r φ γ
  have hLargestEq :
      largestOrderedRepresentativeEigenvalue hRpos hn = hR.eigenvalues ⟨0, hn⟩ := by
    -- Unfold the source-facing endpoint API once and replace the Hermitian proof by proof
    -- irrelevance.
    unfold largestOrderedRepresentativeEigenvalue
    simp
  have hSmallestEq :
      smallestOrderedRepresentativeEigenvalue hRpos hn =
        hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ := by
    -- The lower endpoint uses the same proof-irrelevant Hermitian owner.
    unfold smallestOrderedRepresentativeEigenvalue
    simp
  have hr_ne : r ≠ 0 := by
    intro hr
    apply hrr
    simp [hr]
  have hr_ofLp_ne : r.ofLp ≠ 0 := by
    simpa using hr_ne
  have hrRr : 0 < dotProduct r (R.mulVec r) := by
    -- Positive definiteness makes the self-curvature denominator strictly positive.
    simpa using hRpos.dotProduct_mulVec_pos hr_ofLp_ne
  rcases scaledRepresentativeEndpointInequalities hRpos hn hγ hLower hUpper with
    ⟨hLastScaled, hFirstScaled⟩
  have hLastScaledRaw :
      γ * hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ ≤ 1 := by
    simpa [hSmallestEq] using hLastScaled
  have hFirstScaledRaw :
      1 ≤ γ * hR.eigenvalues ⟨0, hn⟩ := by
    simpa [hLargestEq] using hFirstScaled
  by_cases hLastGe : 1 ≤ γ * smallestOrderedRepresentativeEigenvalue hRpos hn
  · -- If the scaled smallest endpoint is already at least `1`, Theorem 5.5.5 (1) puts the
    -- updated smallest eigenvalue exactly at `1`.
    have hLastGeRaw :
        1 ≤ γ * hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ := by
      simpa [hSmallestEq] using hLastGe
    rcases ssvmInverseUpdate_self_eigenvalues_case_ge_one hR r hrr hrRr hn hφ hγ hLastGeRaw with
      ⟨hUpdatedLastEq, hIntervals⟩
    constructor
    · calc
        γ * smallestOrderedRepresentativeEigenvalue hRpos hn ≤ 1 := hLastScaled
        _ = hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ := by
          symm
          simpa [hRφ] using hUpdatedLastEq
    · by_cases hOne : n = 1
      · -- In dimension `1`, the first and last ordered eigenvalues coincide.
        have hUpdatedFirstEq :
            hRφ.eigenvalues ⟨0, hn⟩ = 1 := by
          subst hOne
          simpa [hRφ] using hUpdatedLastEq
        calc
          hRφ.eigenvalues ⟨0, hn⟩ = 1 := hUpdatedFirstEq
          _ ≤ γ * largestOrderedRepresentativeEigenvalue hRpos hn := by
            subst hOne
            simpa [largestOrderedRepresentativeEigenvalue, smallestOrderedRepresentativeEigenvalue]
              using hLastGe
      · have hOneLt : 1 < n := by
          exact lt_of_le_of_ne (Nat.succ_le_of_lt hn) (by simpa [eq_comm] using hOne)
        have hStep := hIntervals 0 hOneLt
        exact (by simpa [hLargestEq, hRφ] using hStep.2.2 : hRφ.eigenvalues ⟨0, hn⟩ ≤
          γ * largestOrderedRepresentativeEigenvalue hRpos hn)
  · by_cases hFirstLe : γ * largestOrderedRepresentativeEigenvalue hRpos hn ≤ 1
    · -- If the scaled largest endpoint is at most `1`, Theorem 5.5.5 (2) puts the updated
      -- largest eigenvalue exactly at `1`.
      have hFirstLeRaw :
          γ * hR.eigenvalues ⟨0, hn⟩ ≤ 1 := by
        simpa [hLargestEq] using hFirstLe
      rcases ssvmInverseUpdate_self_eigenvalues_case_le_one hR r hrr hrRr hn hφ hγ hFirstLeRaw with
        ⟨hUpdatedFirstEq, hIntervals⟩
      constructor
      · by_cases hOne : n = 1
        · -- In dimension `1`, the first and last ordered eigenvalues coincide.
          have hUpdatedLastEq :
              hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ = 1 := by
            subst hOne
            simpa [hRφ] using hUpdatedFirstEq
          calc
            γ * smallestOrderedRepresentativeEigenvalue hRpos hn ≤ 1 := hLastScaled
            _ = hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ := by
              symm
              exact hUpdatedLastEq
        · have hOneLt : 1 < n := by
            exact lt_of_le_of_ne (Nat.succ_le_of_lt hn) (by simpa [eq_comm] using hOne)
          have hLastIndex : (n - 2) + 1 < n := by
            omega
          have hLastIndexEq : (n - 2) + 1 = n - 1 := by
            omega
          have hStep := hIntervals (n - 2) hLastIndex
          exact (by
            simpa [hSmallestEq, hRφ, hLastIndexEq] using hStep.1 :
              γ * smallestOrderedRepresentativeEigenvalue hRpos hn ≤
                hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩)
      · calc
          hRφ.eigenvalues ⟨0, hn⟩ = 1 := by
            simpa [hRφ] using hUpdatedFirstEq
          _ ≤ γ * largestOrderedRepresentativeEigenvalue hRpos hn := hFirstScaled
    · -- Otherwise the level `1` lies strictly between the scaled endpoints, so invoke
      -- Theorem 5.5.5 (3) at the first adjacent crossing.
      have hFirstNotRaw :
          ¬ γ * hR.eigenvalues ⟨0, hn⟩ ≤ 1 := by
        simpa [hLargestEq] using hFirstLe
      rcases endpointCrossingIndex
          (f := fun i : Fin n ↦ γ * hR.eigenvalues i) hn hLastScaledRaw hFirstNotRaw with
        ⟨k, hk, hCrossLower, hCrossUpper⟩
      rcases ssvmInverseUpdate_self_eigenvalues_case_crossing_one
          hR r hrr hrRr hn hφ hγ hLastScaledRaw hFirstScaledRaw k hk hCrossLower hCrossUpper with
        ⟨hLeft, hCrossTopLower, hCrossTopUpper, hCrossBottomLower, hCrossBottomUpper, hRight, _⟩
      have hUpperBoundRaw :
          hRφ.eigenvalues ⟨0, hn⟩ ≤ γ * hR.eigenvalues ⟨0, hn⟩ := by
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · simpa [hRφ] using hCrossTopUpper
        · have hLeftZero := hLeft 0 (by simpa using hk_pos)
          simpa [hRφ] using hLeftZero.2
      have hLowerBoundRaw :
          γ * hR.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ ≤
            hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ := by
        by_cases hLastIndex : k + 1 = n - 1
        · simpa [hRφ, hLastIndex] using hCrossBottomLower
        · have hjLower : k + 1 ≤ n - 2 := by
            omega
          have hjUpper : (n - 2) + 1 < n := by
            omega
          have hjUpperEq : (n - 2) + 1 = n - 1 := by
            omega
          have hRightLast := hRight (n - 2) hjLower hjUpper
          simpa [hRφ, hjUpperEq] using hRightLast.1
      exact ⟨by simpa [hSmallestEq] using hLowerBoundRaw,
        by simpa [hLargestEq] using hUpperBoundRaw⟩

/-- Chapter05 Corollary 5.5.7: if `φ ∈ Set.Icc (0 : ℝ) 1`, `0 < γ`, the SSVM step in `(5.5.24)`
is nonzero in the sense `dotProduct r r ≠ 0`, and the reciprocal scaling `1 / γ` lies between
the smallest and largest ordered eigenvalues of `R`, then the spectral condition number does not
increase: `κ(R_(k + 1)^φ) ≤ κ(R_k)`. -/
theorem ssvmUpdatedRepresentativeConditionNumber_le
    {R : MatrixN} (hRpos : R.PosDef) (r : Point)
    (hrr : dotProduct r r ≠ 0) {φ γ : ℝ}
    (hn : 0 < n) (hφ : φ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hLower : smallestOrderedRepresentativeEigenvalue hRpos hn ≤ 1 / γ)
    (hUpper : 1 / γ ≤ largestOrderedRepresentativeEigenvalue hRpos hn) :
    ssvmUpdatedRepresentativeConditionNumber r φ γ
        (ssvmInverseUpdate_self_posDef hRpos r hrr hφ hγ) hn ≤
      ssvmRepresentativeConditionNumber hRpos hn := by
  let hRφpos : (ssvmInverseUpdate R r r φ γ).PosDef :=
    ssvmInverseUpdate_self_posDef hRpos r hrr hφ hγ
  let hRφ : (ssvmInverseUpdate R r r φ γ).IsHermitian :=
    ssvmInverseUpdate_self_isHermitian hRpos.isHermitian r φ γ
  let lambda1 := largestOrderedRepresentativeEigenvalue hRpos hn
  let lambdaN := smallestOrderedRepresentativeEigenvalue hRpos hn
  let mu1 := largestOrderedRepresentativeEigenvalue hRφpos hn
  let muN := smallestOrderedRepresentativeEigenvalue hRφpos hn
  have hμLargestEq :
      mu1 = hRφ.eigenvalues ⟨0, hn⟩ := by
    -- Unfold the updated largest endpoint and remove the proof-term mismatch by proof
    -- irrelevance of Hermitianity.
    unfold mu1 largestOrderedRepresentativeEigenvalue
    simp
  have hμSmallestEq :
      muN = hRφ.eigenvalues ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩ := by
    -- The updated smallest endpoint uses the same proof-irrelevant Hermitian owner.
    unfold muN smallestOrderedRepresentativeEigenvalue
    simp
  rcases ssvmUpdatedOrderedEndpointBounds hRpos r hrr hn hφ hγ hLower hUpper with
    ⟨hμLower, hμUpper⟩
  have hLambdaNPos : 0 < lambdaN := by
    -- Positive definiteness of the original representative keeps the denominator positive.
    simpa [lambdaN, smallestOrderedRepresentativeEigenvalue] using
      hRpos.eigenvalues_pos ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩
  have hMuNPos : 0 < muN := by
    -- The updated representative is also positive definite by the previous theorem.
    simpa [muN, smallestOrderedRepresentativeEigenvalue] using
      hRφpos.eigenvalues_pos ⟨n - 1, Nat.sub_lt hn (Nat.succ_pos 0)⟩
  have hBoundNumerator : mu1 ≤ γ * lambda1 := by
    simpa [lambda1, hμLargestEq] using hμUpper
  have hBoundDenominator : γ * lambdaN ≤ muN := by
    simpa [lambdaN, hμSmallestEq] using hμLower
  have hMain :
      mu1 * lambdaN ≤ lambda1 * muN := by
    -- Clear the shared positive scale `γ` at the polynomial level.
    nlinarith [hBoundNumerator, hBoundDenominator, hγ, hLambdaNPos]
  -- Unfold both condition-number definitions and clear the positive denominators.
  change mu1 / muN ≤ lambda1 / lambdaN
  field_simp [hMuNPos.ne', hLambdaNPos.ne']
  nlinarith [hMain]

end

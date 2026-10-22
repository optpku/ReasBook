/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

public section

noncomputable section

open scoped BigOperators

namespace DiscreteEM

universe u v w

variable {Theta : Type u} {X : Type v} {Y : Type w}

/-- The observed marginal PMF `p_Y(·; θ)` obtained from the joint law `joint θ`. -/
def observedPmf (joint : Theta → PMF (X × Y)) (theta : Theta) : PMF Y :=
  PMF.map Prod.snd (joint theta)

/-- The defining finite-sum formula for `observedPmf`, matching equation `(4.48)`. -/
theorem observedPmf_apply_eq_sum
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y) :
    observedPmf joint theta y = ∑ x, joint theta (x, y) := by
  classical
  -- Expand the pushed-forward PMF into the iterated sum over hidden and observed states.
  rw [observedPmf, PMF.map_apply, ENNReal.tsum_prod']
  -- Only the fiber above `y` contributes, and finiteness of `X` turns the outer `tsum` into a sum.
  calc
    (∑' x : X, ∑' y' : Y, if y = (x, y').2 then joint theta (x, y') else 0) =
        ∑' x : X, joint theta (x, y) := by
      refine tsum_congr fun x => ?_
      have hOffDiagonal :
          ∀ y' ≠ y, (if y = (x, y').2 then joint theta (x, y') else 0) = 0 := by
        intro y' hy'
        by_cases h : y = y'
        · subst h
          exact (hy' rfl).elim
        · simp [h]
      exact (tsum_eq_single y hOffDiagonal).trans (by simp)
    _ = ∑ x, joint theta (x, y) := by
      rw [tsum_fintype]

/-- Nonzero joint mass at `(x, y)` forces nonzero observed mass at `y`. -/
theorem observedPmf_ne_zero_of_joint_ne_zero
    (joint : Theta → PMF (X × Y)) (theta : Theta) (x : X) (y : Y)
    (hxy : joint theta (x, y) ≠ 0) :
    observedPmf joint theta y ≠ 0 := by
  have hySupport : y ∈ (observedPmf joint theta).support := by
    rw [observedPmf, PMF.mem_support_map_iff]
    exact ⟨(x, y), ((joint theta).mem_support_iff (x, y)).2 hxy, rfl⟩
  exact ((observedPmf joint theta).mem_support_iff y).1 hySupport

/-- The ratio `joint θ (x, y) / observedPmf joint θ y` has total mass `1` when
`observedPmf joint θ y ≠ 0`. -/
theorem posteriorPmf_mass_eq_one
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) :
    ∑ x, joint theta (x, y) / observedPmf joint theta y = 1 := by
  -- Factor out the constant denominator and rewrite the numerator as the observed marginal.
  calc
    ∑ x, joint theta (x, y) / observedPmf joint theta y =
        ∑ x, joint theta (x, y) * (observedPmf joint theta y)⁻¹ := by
      simp [div_eq_mul_inv]
    _ = (∑ x, joint theta (x, y)) * (observedPmf joint theta y)⁻¹ := by
      rw [Finset.sum_mul]
    _ = observedPmf joint theta y * (observedPmf joint theta y)⁻¹ := by
      rw [observedPmf_apply_eq_sum]
    _ = observedPmf joint theta y / observedPmf joint theta y := by
      rw [div_eq_mul_inv]
    _ = 1 := by
      exact ENNReal.div_self hy (PMF.apply_ne_top (observedPmf joint theta) y)

/-- The conditional hidden-state PMF `p_{X | Y}(· | y; θ)` from equation `(4.47)`. -/
def posteriorPmf
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) : PMF X :=
  PMF.ofFintype
    (fun x ↦ joint theta (x, y) / observedPmf joint theta y)
    (posteriorPmf_mass_eq_one joint theta y hy)

/-- The defining pointwise formula for `posteriorPmf`, matching equation `(4.47)`. -/
theorem posteriorPmf_apply
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (x : X) :
    posteriorPmf joint theta y hy x = joint theta (x, y) / observedPmf joint theta y := by
  rfl

/-- Helper for Notation 4.5-extra-1: the real posterior weights sum to `1`. -/
private theorem posteriorPmfToRealSumEqOne
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) :
    ∑ x, (posteriorPmf joint theta y hy x).toReal = 1 := by
  have hMass : ∑ x, posteriorPmf joint theta y hy x = 1 := by
    simpa [posteriorPmf_apply] using posteriorPmf_mass_eq_one joint theta y hy
  -- Convert the finite `ENNReal` normalization of the posterior into a real-valued one.
  calc
    ∑ x, (posteriorPmf joint theta y hy x).toReal =
        ENNReal.toReal (∑ x, posteriorPmf joint theta y hy x) := by
      symm
      exact ENNReal.toReal_sum fun x _ => PMF.apply_ne_top (posteriorPmf joint theta y hy) x
    _ = 1 := by rw [hMass, ENNReal.toReal_one]

/-- The observed-data log-likelihood `log (observedPmf joint θ y)`. -/
def observedLogLikelihood (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y) : ℝ :=
  Real.log ((observedPmf joint theta y).toReal)

/-- The defining formula for `observedLogLikelihood`. -/
theorem observedLogLikelihood_def
    (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y) :
    observedLogLikelihood joint theta y = Real.log ((observedPmf joint theta y).toReal) := by
  rfl

/-- The complete-data log-likelihood `log (joint θ (x, y))`. -/
def completeLogLikelihood
    (joint : Theta → PMF (X × Y)) (theta : Theta) (x : X) (y : Y) : ℝ :=
  Real.log ((joint theta (x, y)).toReal)

/-- The defining formula for `completeLogLikelihood`. -/
theorem completeLogLikelihood_def
    (joint : Theta → PMF (X × Y)) (theta : Theta) (x : X) (y : Y) :
    completeLogLikelihood joint theta x y = Real.log ((joint theta (x, y)).toReal) := by
  rfl

/-- The conditional log-likelihood `log (posteriorPmf joint θ y hy x)`. -/
def conditionalLogLikelihood
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (x : X) : ℝ :=
  Real.log ((posteriorPmf joint theta y hy x).toReal)

/-- The defining formula for `conditionalLogLikelihood`. -/
theorem conditionalLogLikelihood_def
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (x : X) :
    conditionalLogLikelihood joint theta y hy x =
      Real.log ((posteriorPmf joint theta y hy x).toReal) := by
  rfl

/-- `conditionalLogLikelihood` is independent of the chosen proof that
`observedPmf joint θ y ≠ 0`. -/
theorem conditionalLogLikelihood_congr_nonvanishing
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    {hy hy' : observedPmf joint theta y ≠ 0} (x : X) :
    conditionalLogLikelihood joint theta y hy x =
      conditionalLogLikelihood joint theta y hy' x := by
  simp [conditionalLogLikelihood, posteriorPmf_apply]

/-- The E-step functional `Q(θ | y; θ_v)` obtained by averaging the complete-data
log-likelihood against the posterior at `thetaV`. -/
def qFunction
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hV : observedPmf joint thetaV y ≠ 0) : ℝ :=
  ∑ x, (posteriorPmf joint thetaV y hV x).toReal * completeLogLikelihood joint theta x y

/-- The defining finite-sum formula for `qFunction`. -/
theorem qFunction_def
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hV : observedPmf joint thetaV y ≠ 0) :
    qFunction joint theta thetaV y hV =
      ∑ x,
        (posteriorPmf joint thetaV y hV x).toReal * completeLogLikelihood joint theta x y := by
  rfl

/-- The entropy-style correction term `H(θ | y; θ_v)` obtained by averaging the
conditional log-likelihood at `theta` against the posterior at `thetaV`. -/
def hFunction
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (hV : observedPmf joint thetaV y ≠ 0) : ℝ :=
  ∑ x, (posteriorPmf joint thetaV y hV x).toReal * conditionalLogLikelihood joint theta y hy x

/-- The defining finite-sum formula for `hFunction`. -/
theorem hFunction_def
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (hV : observedPmf joint thetaV y ≠ 0) :
    hFunction joint theta thetaV y hy hV =
      ∑ x, (posteriorPmf joint thetaV y hV x).toReal *
        conditionalLogLikelihood joint theta y hy x := by
  rfl

/-- `hFunction` is independent of the chosen proof that
`observedPmf joint θ y ≠ 0`. -/
theorem hFunction_congr_nonvanishing
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    {hy hy' : observedPmf joint theta y ≠ 0} (hV : observedPmf joint thetaV y ≠ 0) :
    hFunction joint theta thetaV y hy hV = hFunction joint theta thetaV y hy' hV := by
  simp [hFunction, conditionalLogLikelihood, posteriorPmf_apply]

/-- Under the EM support condition, the candidate parameter `theta` also assigns
nonzero observed mass to `y`. -/
theorem observedPmf_ne_zero_of_posterior_support
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hV : observedPmf joint thetaV y ≠ 0)
    (hSupport : ∀ x, posteriorPmf joint thetaV y hV x ≠ 0 → joint theta (x, y) ≠ 0) :
    observedPmf joint theta y ≠ 0 := by
  obtain ⟨x, hx⟩ := (posteriorPmf joint thetaV y hV).support_nonempty
  exact observedPmf_ne_zero_of_joint_ne_zero joint theta x y <|
    hSupport x (((posteriorPmf joint thetaV y hV).mem_support_iff x).1 hx)

/-- The pointwise identity `l_Y = l_(X,Y) - l_(X|Y)` on pairs `(x, y)` where
`joint θ (x, y) ≠ 0`. -/
theorem observedLogLikelihood_eq_complete_sub_conditional
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (x : X) (hxy : joint theta (x, y) ≠ 0) :
    observedLogLikelihood joint theta y =
      completeLogLikelihood joint theta x y -
        conditionalLogLikelihood joint theta y
          (observedPmf_ne_zero_of_joint_ne_zero joint theta x y hxy) x := by
  let hy : observedPmf joint theta y ≠ 0 :=
    observedPmf_ne_zero_of_joint_ne_zero joint theta x y hxy
  have hxyReal : (joint theta (x, y)).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.2 ⟨hxy, PMF.apply_ne_top (joint theta) (x, y)⟩
  have hyReal : (observedPmf joint theta y).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.2 ⟨hy, PMF.apply_ne_top (observedPmf joint theta) y⟩
  -- Rewrite the conditional term using the posterior ratio, then apply `log_div`.
  rw [observedLogLikelihood_def, completeLogLikelihood_def, conditionalLogLikelihood_def]
  rw [posteriorPmf_apply, ENNReal.toReal_div, Real.log_div hxyReal hyReal]
  ring

/-- Bridge form of `observedLogLikelihood_eq_complete_sub_conditional` using an
explicit proof that `observedPmf joint θ y ≠ 0`. -/
theorem observedLogLikelihood_eq_complete_sub_conditional_of_nonvanishing
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta : Theta) (y : Y)
    (hy : observedPmf joint theta y ≠ 0) (x : X) (hxy : joint theta (x, y) ≠ 0) :
    observedLogLikelihood joint theta y =
      completeLogLikelihood joint theta x y - conditionalLogLikelihood joint theta y hy x := by
  have hcond :
      conditionalLogLikelihood joint theta y
        (observedPmf_ne_zero_of_joint_ne_zero joint theta x y hxy) x =
        conditionalLogLikelihood joint theta y hy x := by
    simp [conditionalLogLikelihood, posteriorPmf_apply]
  calc
    observedLogLikelihood joint theta y =
        completeLogLikelihood joint theta x y -
          conditionalLogLikelihood joint theta y
            (observedPmf_ne_zero_of_joint_ne_zero joint theta x y hxy) x :=
      observedLogLikelihood_eq_complete_sub_conditional joint theta y x hxy
    _ = completeLogLikelihood joint theta x y - conditionalLogLikelihood joint theta y hy x := by
      rw [hcond]

/- Notation 4.5-extra-1: the discrete EM notation is owned by the PMF-level declarations
`DiscreteEM.observedPmf`, `DiscreteEM.posteriorPmf`, `DiscreteEM.observedLogLikelihood`,
`DiscreteEM.completeLogLikelihood`, `DiscreteEM.conditionalLogLikelihood`,
`DiscreteEM.qFunction`, `DiscreteEM.hFunction`, and the averaged decomposition theorem
`DiscreteEM.observedLogLikelihood_eq_qFunction_sub_hFunction`.
-/
/-- Notation 4.5-extra-1: the source EM decomposition
`observedLogLikelihood joint θ y = qFunction joint θ θ_v y hV - hFunction joint θ θ_v y hy hV`
under the support condition that every hidden state with positive posterior weight at `thetaV`
also has positive joint mass at `theta`. -/
theorem observedLogLikelihood_eq_qFunction_sub_hFunction
    [Fintype X] (joint : Theta → PMF (X × Y)) (theta thetaV : Theta) (y : Y)
    (hV : observedPmf joint thetaV y ≠ 0)
    (hSupport : ∀ x, posteriorPmf joint thetaV y hV x ≠ 0 → joint theta (x, y) ≠ 0) :
    observedLogLikelihood joint theta y =
      qFunction joint theta thetaV y hV -
        hFunction joint theta thetaV y
          (observedPmf_ne_zero_of_posterior_support joint theta thetaV y hV hSupport) hV := by
  let hy : observedPmf joint theta y ≠ 0 :=
    observedPmf_ne_zero_of_posterior_support joint theta thetaV y hV hSupport
  have weightedPointwise :
      ∀ x,
        (posteriorPmf joint thetaV y hV x).toReal * observedLogLikelihood joint theta y =
          (posteriorPmf joint thetaV y hV x).toReal *
              completeLogLikelihood joint theta x y -
            (posteriorPmf joint thetaV y hV x).toReal *
              conditionalLogLikelihood joint theta y hy x := by
    intro x
    by_cases hx : posteriorPmf joint thetaV y hV x = 0
    · -- Off posterior support, the weight is zero and the identity is trivial.
      simp [hx]
    · -- On posterior support, use the pointwise likelihood decomposition and
      -- then distribute the weight.
      have hxy : joint theta (x, y) ≠ 0 := hSupport x hx
      calc
        (posteriorPmf joint thetaV y hV x).toReal * observedLogLikelihood joint theta y =
            (posteriorPmf joint thetaV y hV x).toReal *
              (completeLogLikelihood joint theta x y -
                conditionalLogLikelihood joint theta y hy x) := by
          rw [
            observedLogLikelihood_eq_complete_sub_conditional_of_nonvanishing
              joint theta y hy x hxy
          ]
        _ =
            (posteriorPmf joint thetaV y hV x).toReal *
                completeLogLikelihood joint theta x y -
              (posteriorPmf joint thetaV y hV x).toReal *
                conditionalLogLikelihood joint theta y hy x := by
          ring
  -- Normalize the posterior weights so the constant observed likelihood becomes a weighted sum.
  calc
    observedLogLikelihood joint theta y = 1 * observedLogLikelihood joint theta y := by ring
    _ =
        (∑ x, (posteriorPmf joint thetaV y hV x).toReal) *
          observedLogLikelihood joint theta y := by
      rw [posteriorPmfToRealSumEqOne joint thetaV y hV]
    _ = ∑ x, (posteriorPmf joint thetaV y hV x).toReal * observedLogLikelihood joint theta y := by
      rw [Finset.sum_mul]
    _ =
        ∑ x,
          ((posteriorPmf joint thetaV y hV x).toReal *
                completeLogLikelihood joint theta x y -
              (posteriorPmf joint thetaV y hV x).toReal *
                conditionalLogLikelihood joint theta y hy x) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      exact weightedPointwise x
    _ =
        (∑ x,
            (posteriorPmf joint thetaV y hV x).toReal *
              completeLogLikelihood joint theta x y) -
          ∑ x,
            (posteriorPmf joint thetaV y hV x).toReal *
              conditionalLogLikelihood joint theta y hy x := by
      rw [Finset.sum_sub_distrib]
    _ = qFunction joint theta thetaV y hV - hFunction joint theta thetaV y hy hV := by
      rw [qFunction_def, hFunction_def]

end DiscreteEM

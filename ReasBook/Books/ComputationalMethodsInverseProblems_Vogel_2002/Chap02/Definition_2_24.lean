/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_22.WeakSeqTendsto
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Semicontinuity.Basic

public section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 2.24. A functional `J : H → ℝ` is weakly lower semicontinuous if
`J fStar ≤ Filter.liminf (fun n ↦ (J (f n) : EReal)) Filter.atTop` whenever `f` converges
weakly to `fStar`; the source liminf is the ordinary sequence liminf, so it is taken in
`EReal` to allow the value `+∞`. -/
def weakLowerSemicontinuous (J : H → ℝ) : Prop :=
  ∀ {f : ℕ → H} {fStar : H}, weakSeqTendsto f fStar →
    J fStar ≤ Filter.liminf (fun n ↦ (J (f n) : EReal)) Filter.atTop

/-- A functional `J : H → ℝ` is weakly lower semicontinuous if
`J fStar ≤ Filter.liminf (fun n ↦ (J (f n) : EReal)) Filter.atTop` whenever `f` converges weakly
to `fStar`; the source liminf is the ordinary sequence liminf, so it is taken in `EReal` to allow
the value `+∞`. -/
theorem weakLowerSemicontinuous_iff {J : H → ℝ} :
    weakLowerSemicontinuous J ↔
      ∀ {f : ℕ → H} {fStar : H}, weakSeqTendsto f fStar →
        J fStar ≤ Filter.liminf (fun n ↦ (J (f n) : EReal)) Filter.atTop :=
  Iff.rfl

/-- Helper for Definition 2.24: lower semicontinuity at `x` gives an `EReal` liminf lower bound
along every convergent filter. -/
theorem LowerSemicontinuousAt.leLiminfEReal_of_tendsto {α ι : Type*} [TopologicalSpace α]
    {f : α → ℝ} {x : α} {u : ι → α} {F : Filter ι} (hf : LowerSemicontinuousAt f x)
    (hu : Filter.Tendsto u F (nhds x)) :
    (f x : EReal) ≤ Filter.liminf (fun i ↦ (f (u i) : EReal)) F := by
  -- Reduce the liminf comparison to eventual lower bounds below `f x`.
  rw [Filter.le_liminf_iff']
  intro y hy
  -- Choose a real threshold strictly between `y` and `f x`.
  obtain ⟨z, hyz, hzfx⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have hzfx' : z < f x := EReal.coe_lt_coe_iff.1 hzfx
  have hzEventually : ∀ᶠ x' in nhds x, z < f x' := (lowerSemicontinuousAt_iff.1 hf) z hzfx'
  -- Push the eventual lower bound forward along the convergent map `u`.
  filter_upwards [hu hzEventually] with i hi
  exact le_of_lt (hyz.trans (EReal.coe_lt_coe_iff.2 hi))

/-- A lower semicontinuous functional on `WeakSpace ℝ H` is weakly lower semicontinuous after
pulling back along `toWeakSpace ℝ H : H ≃ₗ[ℝ] WeakSpace ℝ H`. -/
theorem LowerSemicontinuous.weakLowerSemicontinuous {J : WeakSpace ℝ H → ℝ}
    (hJ : LowerSemicontinuous J) :
    weakLowerSemicontinuous (fun f : H ↦ J (toWeakSpace ℝ H f)) := by
  intro f fStar hf
  -- Reinterpret weak sequential convergence as ordinary convergence in `WeakSpace`.
  rw [weakSeqTendsto_iff] at hf
  -- Apply the generic liminf bridge at the weak-space limit point.
  simpa using
    (LowerSemicontinuousAt.leLiminfEReal_of_tendsto
      (f := J) (x := toWeakSpace ℝ H fStar) (u := fun n ↦ toWeakSpace ℝ H (f n))
      (F := Filter.atTop) (hJ (toWeakSpace ℝ H fStar)) hf)

/-- Lower semicontinuity of `J` on `WeakSpace ℝ H` implies weak lower semicontinuity in the sense
of Definition 2.24. -/
theorem weakLowerSemicontinuous_of_lowerSemicontinuousWeakSpace {J : H → ℝ}
    (hJ : LowerSemicontinuous
      (fun x : WeakSpace ℝ H ↦ J ((toWeakSpace ℝ H).symm x))) :
    weakLowerSemicontinuous J := by
  intro f fStar hf
  -- Apply the weak-space theorem to the pulled-back functional and simplify the equivalence.
  simpa using
    (LowerSemicontinuous.weakLowerSemicontinuous
      (H := H) (J := fun x : WeakSpace ℝ H ↦ J ((toWeakSpace ℝ H).symm x)) hJ hf)

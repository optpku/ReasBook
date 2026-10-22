/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

section

variable {X : Type u}

/-- The source-facing real epigraph of an extended-real-valued function. -/
def realEpigraph (f : X → EReal) : Set (X × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

@[simp] theorem mem_realEpigraph {f : X → EReal} {x : X} {y : ℝ} :
    (x, y) ∈ realEpigraph f ↔ f x ≤ (y : EReal) :=
  Iff.rfl

/-- The source-facing real epigraph is the preimage of the canonical `EReal` epigraph under the
height inclusion `ℝ → EReal`. -/
theorem realEpigraph_eq_preimage_epigraph (f : X → EReal) :
    realEpigraph f =
      (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) ⁻¹' {p : X × EReal | f p.1 ≤ p.2} := by
  ext p
  rfl

end

section

variable {X : Type u} [TopologicalSpace X]

omit [TopologicalSpace X] in
/-- Helper for Theorem 2.2: the `⊥`-sublevel set is the intersection of all real sublevel sets. -/
lemma preimage_Iic_bot_eq_iInter_realSublevelSets (f : X → EReal) :
    f ⁻¹' Iic (⊥ : EReal) = ⋂ a : ℝ, f ⁻¹' Iic (a : EReal) := by
  ext x
  constructor
  · intro hx
    -- A point below `⊥` is below every real threshold.
    simp only [mem_preimage, mem_Iic, mem_iInter]
    intro a
    exact hx.trans bot_le
  · intro hx
    -- If `f x` were strictly above `⊥`, a real number would lie below it.
    simp only [mem_preimage, mem_Iic, mem_iInter] at hx ⊢
    by_contra hbot
    have hlt : (⊥ : EReal) < f x := lt_of_not_ge hbot
    rcases EReal.lt_iff_exists_real_btwn.1 hlt with ⟨a, -, ha⟩
    exact (not_le_of_gt ha) (hx a)

/-- Helper for Theorem 2.2: closedness of the real sublevel sets implies closedness of every
`EReal` sublevel set. -/
lemma isClosed_erealSublevelSet_of_isClosed_realSublevelSets {f : X → EReal}
    (h : ∀ a : ℝ, IsClosed (f ⁻¹' Iic (a : EReal))) :
    ∀ b : EReal, IsClosed (f ⁻¹' Iic b) := by
  -- Split the threshold into `⊥`, a real value, or `⊤`.
  refine EReal.rec ?_ (fun a ↦ h a) ?_
  · -- The bottom sublevel is an intersection of the real sublevels.
    rw [preimage_Iic_bot_eq_iInter_realSublevelSets]
    exact isClosed_iInter h
  · -- The top sublevel is all of `X`.
    simp

/-- Helper for Theorem 2.2: a closed real epigraph has closed real sections, hence closed real
sublevel sets. -/
lemma isClosed_realSublevelSet_of_isClosed_realEpigraph {f : X → EReal}
    (hEpi : IsClosed (realEpigraph f)) (a : ℝ) :
    IsClosed (f ⁻¹' Iic (a : EReal)) := by
  -- Pull back the real epigraph along the constant-height section map `x ↦ (x, a)`.
  have hcont : Continuous (fun x : X ↦ (x, a)) :=
    continuous_id.prodMk continuous_const
  simpa [realEpigraph] using hEpi.preimage hcont

-- Proof sketch: compare the real epigraph with the canonical `EReal`-valued epigraph via the
-- continuous embedding `ℝ → EReal`, then invoke
-- `lowerSemicontinuous_iff_isClosed_epigraph`.
/-- A function `f : X → EReal` is lower semicontinuous exactly when its real epigraph is closed. -/
theorem lowerSemicontinuous_iff_isClosed_real_epigraph (f : X → EReal) :
    LowerSemicontinuous f ↔ IsClosed (realEpigraph f) := by
  constructor
  · intro hf
    -- Pull back the canonical closed epigraph along the height inclusion `ℝ → EReal`.
    have hClosed :
        IsClosed {p : X × EReal | f p.1 ≤ p.2} :=
      (lowerSemicontinuous_iff_isClosed_epigraph (f := f)).1 hf
    have hcont : Continuous (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    simpa [realEpigraph_eq_preimage_epigraph] using hClosed.preimage hcont
  · intro hReal
    -- Route correction: closedness does not push backward across the height-inclusion preimage,
    -- so instead recover the real sublevel sets as closed sections of the real epigraph.
    refine (lowerSemicontinuous_iff_isClosed_preimage).2 ?_
    exact isClosed_erealSublevelSet_of_isClosed_realSublevelSets
      (fun a ↦ isClosed_realSublevelSet_of_isClosed_realEpigraph hReal a)

alias ⟨LowerSemicontinuous.isClosed_real_epigraph, isClosed_real_epigraph_iff_lowerSemicontinuous⟩
  := lowerSemicontinuous_iff_isClosed_real_epigraph

-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_preimage` for the easy direction, and for
-- the converse recover the `EReal`-sublevel sets from the real ones, treating `⊤` trivially and
-- `⊥` as an intersection of real sublevel sets.
/-- A function `f : X → EReal` is lower semicontinuous exactly when all of its real sublevel sets
are closed. -/
theorem lowerSemicontinuous_iff_isClosed_real_sublevelSets (f : X → EReal) :
    LowerSemicontinuous f ↔ ∀ a : ℝ, IsClosed (f ⁻¹' Iic (a : EReal)) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  constructor
  · intro hf a
    -- Restrict the closed-preimage characterization to real thresholds.
    exact hf (a : EReal)
  · intro h
    -- Upgrade the real-threshold hypothesis to all `EReal` thresholds.
    exact isClosed_erealSublevelSet_of_isClosed_realSublevelSets h

/-- A lower semicontinuous extended-real-valued function has closed real sublevel sets. -/
theorem LowerSemicontinuous.isClosed_real_sublevelSet {f : X → EReal}
    (hf : LowerSemicontinuous f) (a : ℝ) :
    IsClosed (f ⁻¹' Iic (a : EReal)) :=
  (lowerSemicontinuous_iff_isClosed_real_sublevelSets f).1 hf a

-- Proof sketch: combine `lowerSemicontinuous_iff_isClosed_real_epigraph` with
-- `lowerSemicontinuous_iff_isClosed_real_sublevelSets` and apply `List.TFAE`.
/-- Theorem 2.2: for an extended real-valued function, lower semicontinuity, closedness of the
real epigraph, and closedness of all real sublevel sets are equivalent. -/
theorem ereal_lowerSemicontinuous_tfae (f : X → EReal) :
    List.TFAE
      [LowerSemicontinuous f,
        IsClosed (realEpigraph f),
        ∀ a : ℝ, IsClosed (f ⁻¹' Iic (a : EReal))] := by
  -- Use lower semicontinuity as the pivot proposition for the three-way equivalence.
  refine List.tfae_of_forall (LowerSemicontinuous f)
    [LowerSemicontinuous f,
      IsClosed (realEpigraph f),
      ∀ a : ℝ, IsClosed (f ⁻¹' Iic (a : EReal))] ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | ha
  · rfl
  · rcases ha with rfl | ha
    · exact (lowerSemicontinuous_iff_isClosed_real_epigraph f).symm
    · rcases ha with rfl | ha
      · exact (lowerSemicontinuous_iff_isClosed_real_sublevelSets f).symm
      · cases ha

end

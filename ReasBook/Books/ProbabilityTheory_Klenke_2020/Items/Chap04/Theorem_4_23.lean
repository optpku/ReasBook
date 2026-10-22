/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory BoxIntegral intervalIntegral

-- Proof sketch: `Fin 1` has a unique coordinate, so the componentwise inequality needed for
-- `Box.mk` is exactly the hypothesis `a < b`.
/-- The coordinatewise strict inequality needed to build the one-dimensional box attached to the
real interval `(a, b]`. -/
private theorem realIntervalBox_lower_lt_upper (a b : ℝ) (hab : a < b) :
    ∀ i : Fin 1, (![a] : Fin 1 → ℝ) i < (![b] : Fin 1 → ℝ) i := by
  -- `Fin 1` has a single coordinate, so the componentwise inequality is exactly `hab`.
  intro i
  fin_cases i
  simpa using hab

/-- The one-dimensional `Box` whose closed hull is the interval `[a, b]`. -/
def realIntervalBox (a b : ℝ) (hab : a < b) : Box (Fin 1) :=
  Box.mk ![a] ![b] (realIntervalBox_lower_lt_upper a b hab)

/-- Riemann integrability on `[0,1]`, encoded via the chapter's canonical one-dimensional box
model. This abbreviation is the chapter's interval-facing name for the recurring box-integrability
hypothesis. -/
abbrev RiemannIntegrableOnUnitInterval (f : ℝ → ℝ) : Prop :=
  Integrable (realIntervalBox 0 1 zero_lt_one) IntegrationParams.Riemann
    (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul

-- Proof sketch: unfold `realIntervalBox` and `Box.Icc`, then use that every point of `Fin 1 → ℝ`
-- is determined by its unique coordinate.
private theorem realIntervalBox_Icc_eq (a b : ℝ) (hab : a < b) :
    Box.Icc (realIntervalBox a b hab) = Set.Icc ![a] ![b] := by
  -- The closed hull of the box is definitionally the closed interval between its endpoints.
  rfl

/-- Helper for Theorem 4.23: the one-dimensional box `realIntervalBox a b hab` is exactly the
half-open interval `(a, b]` in the `Fin 1` model. -/
private theorem realIntervalBox_coe_eq (a b : ℝ) (hab : a < b) :
    (realIntervalBox a b hab : Set (Fin 1 → ℝ)) = Set.Ioc ![a] ![b] := by
  -- Unfold the box membership conditions and use that `Fin 1` has a single coordinate.
  ext x
  constructor
  · intro hx
    have hx' : a < x 0 ∧ x 0 ≤ b := by
      simpa [realIntervalBox, Box.mem_mk, Set.mem_Ioc, Pi.lt_def, Pi.le_def] using hx
    have hx'' : (a ≤ x 0 ∧ a < x 0) ∧ x 0 ≤ b := ⟨⟨hx'.1.le, hx'.1⟩, hx'.2⟩
    simpa [realIntervalBox, Box.mem_mk, Set.mem_Ioc, Pi.lt_def, Pi.le_def] using hx''
  · intro hx
    have hx' : (a ≤ x 0 ∧ a < x 0) ∧ x 0 ≤ b := by
      simpa [realIntervalBox, Box.mem_mk, Set.mem_Ioc, Pi.lt_def, Pi.le_def] using hx
    intro i
    fin_cases i
    exact ⟨hx'.1.2, hx'.2⟩

/-- Helper for Theorem 4.23: transport the set integral over the one-dimensional `Fin 1` box model
to the ordinary set integral over the corresponding real interval. -/
private lemma setIntegral_Icc_funUnique_eq {f : ℝ → ℝ} {a b : ℝ} :
    (∫ x in Set.Icc ![a] ![b], f (x 0) ∂volume) = ∫ x in Set.Icc a b, f x ∂volume := by
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ f (x 0)
  have h_transport : ∀ (u v : Fin 1 → ℝ) (h : (Fin 1 → ℝ) → ℝ),
      ∫ x in Set.Icc u v, h x ∂volume = ∫ x in Set.Icc (u 0) (v 0), h (fun _ ↦ x) ∂volume :=
    fun u v h ↦ by
      -- The measurable equivalence `Fin 1 → ℝ ≃ᵐ ℝ` preserves volume and sends `Icc u v` to the
      -- real interval `Icc (u 0) (v 0)`.
      convert
        (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _) h _).symm
      exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Icc u v).symm
  simpa [g] using h_transport ![a] ![b] g

/-- Helper for Theorem 4.23: transport the set integral over the one-dimensional `Fin 1` open box
model to the ordinary set integral over the corresponding half-open real interval. -/
private lemma setIntegral_Ioc_funUnique_eq {f : ℝ → ℝ} {a b : ℝ} :
    (∫ x in Set.Ioc ![a] ![b], f (x 0) ∂volume) = ∫ x in Set.Ioc a b, f x ∂volume := by
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ f (x 0)
  have h_transport : ∀ (u v : Fin 1 → ℝ) (h : (Fin 1 → ℝ) → ℝ),
      ∫ x in Set.Ioc u v, h x ∂volume = ∫ x in Set.Ioc (u 0) (v 0), h (fun _ ↦ x) ∂volume :=
    fun u v h ↦ by
      -- The unique-coordinate measurable equivalence also transports half-open intervals.
      convert
        (((MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ).symm _).setIntegral_preimage_emb
          (MeasurableEquiv.measurableEmbedding _) h _).symm
      exact ((OrderIso.funUnique (Fin 1) ℝ).symm.preimage_Ioc u v).symm
  simpa [g] using h_transport ![a] ![b] g

/-- Helper for Theorem 4.23: transport Lebesgue integrability between the one-dimensional `Fin 1`
box model and the ordinary real interval. -/
private lemma integrableOn_Icc_funUnique_iff {f : ℝ → ℝ} {a b : ℝ} :
    IntegrableOn (fun x : Fin 1 → ℝ ↦ f (x 0)) (Set.Icc ![a] ![b]) volume ↔
      IntegrableOn f (Set.Icc a b) volume := by
  let e : (Fin 1 → ℝ) → ℝ := fun x ↦ x 0
  have he : MeasurableEmbedding e :=
    MeasurableEquiv.measurableEmbedding (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hp : MeasurePreserving e volume volume :=
    MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  have himage : e '' Set.Icc ![a] ![b] = Set.Icc a b := by
    -- The unique coordinate identifies the `Fin 1` interval with the ordinary real interval.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [Set.mem_Icc, Pi.le_def] using hx
    · intro hy
      refine ⟨fun _ ↦ y, ?_, rfl⟩
      simpa [Set.mem_Icc, Pi.le_def] using hy
  -- Apply measure-preserving transport along the unique-coordinate equivalence.
  simpa [e, himage] using
    (hp.integrableOn_image he (f := f) (s := Set.Icc ![a] ![b])).symm

/-- Helper for Theorem 4.23: transport Lebesgue integrability between the one-dimensional `Fin 1`
open box model and the ordinary real half-open interval. -/
private lemma integrableOn_Ioc_funUnique_iff {f : ℝ → ℝ} {a b : ℝ} :
    IntegrableOn (fun x : Fin 1 → ℝ ↦ f (x 0)) (Set.Ioc ![a] ![b]) volume ↔
      IntegrableOn f (Set.Ioc a b) volume := by
  let e : (Fin 1 → ℝ) → ℝ := fun x ↦ x 0
  have he : MeasurableEmbedding e :=
    MeasurableEquiv.measurableEmbedding (MeasurableEquiv.funUnique (Fin 1) ℝ)
  have hp : MeasurePreserving e volume volume :=
    MeasureTheory.volume_preserving_funUnique (Fin 1) ℝ
  have himage : e '' Set.Ioc ![a] ![b] = Set.Ioc a b := by
    -- The unique coordinate identifies the `Fin 1` half-open interval with the ordinary one.
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : (a ≤ x 0 ∧ a < x 0) ∧ x 0 ≤ b := by
        simpa [e, Set.mem_Ioc, Pi.lt_def, Pi.le_def] using hx
      exact ⟨hx'.1.2, hx'.2⟩
    · intro hy
      refine ⟨fun _ ↦ y, ?_, rfl⟩
      have hy' : (a ≤ y ∧ a < y) ∧ y ≤ b := ⟨⟨hy.1.le, hy.1⟩, hy.2⟩
      simpa [e, Set.mem_Ioc, Pi.lt_def, Pi.le_def] using hy'
  -- Apply the same measure-preserving transport as in the closed-interval case.
  simpa [e, himage] using
    (hp.integrableOn_image he (f := f) (s := Set.Ioc ![a] ![b])).symm

/-- Helper for Theorem 4.23: retag a tagged prepartition at one chosen box while keeping the
underlying prepartition fixed. -/
private def retaggedAt {ι : Type*} [Fintype ι] [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) {J : Box ι} (x : ι → ℝ) (hxI : x ∈ Box.Icc I) :
    TaggedPrepartition I :=
  { toPrepartition := π.toPrepartition
    tag := Function.update π.tag J x
    tag_mem_Icc := fun K ↦ by
      by_cases hK : K = J
      · subst hK
        simpa [Function.update_self] using hxI
      · simpa [Function.update_of_ne hK] using π.tag_mem_Icc K }

/-- Helper for Theorem 4.23: away from the retagged box, `retaggedAt` keeps the original tags. -/
private lemma retaggedAt_tag_of_ne {ι : Type*} [Fintype ι] [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) {J K : Box ι} {x : ι → ℝ} {hxI : x ∈ Box.Icc I} (hK : K ≠ J) :
    (retaggedAt π (J := J) x hxI).tag K = π.tag K := by
  simp [retaggedAt, Function.update_of_ne hK]

/-- Helper for Theorem 4.23: on the chosen box, `retaggedAt` replaces the old tag by the new one. -/
private lemma retaggedAt_tag_self {ι : Type*} [Fintype ι] [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) {J : Box ι} {x : ι → ℝ} {hxI : x ∈ Box.Icc I} :
    (retaggedAt π (J := J) x hxI).tag J = x := by
  simp [retaggedAt]

/-- Helper for Theorem 4.23: retagging a single box changes the integral sum exactly by that
single-box contribution. -/
private lemma integralSum_retaggedAt_sub_eq {ι : Type*} [Fintype ι] {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [DecidableEq (Box ι)] {I : Box ι} (π : TaggedPrepartition I) {J : Box ι} (hJ : J ∈ π)
    {f : (ι → ℝ) → E} {vol : ι →ᵇᵃ E →L[ℝ] F} {x : ι → ℝ} {hxI : x ∈ Box.Icc I} :
    integralSum f vol (retaggedAt π (J := J) x hxI) - integralSum f vol π =
      vol J (f x - f (π.tag J)) := by
  -- Rewrite both sums over the same underlying boxes and isolate the unique box whose tag changed.
  simp only [integralSum, retaggedAt]
  rw [← Finset.sum_sub_distrib]
  have h_single :
      ∑ K ∈ π.boxes,
        (vol K (f ((retaggedAt π (J := J) x hxI).tag K)) - vol K (f (π.tag K))) =
        vol J (f ((retaggedAt π (J := J) x hxI).tag J)) - vol J (f (π.tag J)) := by
    refine Finset.sum_eq_single_of_mem J hJ ?_
    · intro K hK hKJ
      rw [retaggedAt_tag_of_ne π (J := J) (K := K) (x := x) (hxI := hxI) hKJ]
      simp
  calc
    ∑ K ∈ π.boxes,
        (vol K (f ((retaggedAt π (J := J) x hxI).tag K)) - vol K (f (π.tag K))) =
        vol J (f ((retaggedAt π (J := J) x hxI).tag J)) - vol J (f (π.tag J)) := h_single
    _ = vol J (f x) - vol J (f (π.tag J)) := by
      rw [retaggedAt_tag_self π (J := J) (x := x) (hxI := hxI)]
    _ = vol J (f x - f (π.tag J)) := by rw [(vol J).map_sub]

/-- Helper for Theorem 4.23: if a tagged prepartition is subordinate to the constant radius
`r / 2`, then retagging one box by another point of the same box keeps it subordinate to the
constant radius `r`. -/
private lemma retaggedAt_isSubordinate_const {ι : Type*} [Fintype ι] [DecidableEq (Box ι)]
    {I : Box ι} (π : TaggedPrepartition I) {J : Box ι} (hJ : J ∈ π) {r : ℝ} (hr : 0 < r)
    (hr2 : 0 < r / 2) (hsub : π.IsSubordinate (fun _ : ι → ℝ ↦ ⟨r / 2, hr2⟩)) {x : ι → ℝ}
    (hx : x ∈ Box.Icc J) (hxI : x ∈ Box.Icc I) :
    (retaggedAt π (J := J) x hxI).IsSubordinate (fun _ : ι → ℝ ↦ ⟨r, hr⟩) := by
  -- On the modified box, use the triangle inequality inside the old `r / 2`-ball.
  intro K hK y hy
  by_cases hKJ : K = J
  · subst K
    rw [retaggedAt_tag_self π (J := J) (x := x) (hxI := hxI), Metric.mem_closedBall]
    have hy' : dist y (π.tag J) ≤ r / 2 := by
      exact Metric.mem_closedBall.1 (hsub J hJ hy)
    have hx' : dist (π.tag J) x ≤ r / 2 := by
      simpa [dist_comm] using Metric.mem_closedBall.1 (hsub J hJ hx)
    calc
      dist y x ≤ dist y (π.tag J) + dist (π.tag J) x := dist_triangle _ _ _
      _ ≤ r / 2 + r / 2 := add_le_add hy' hx'
      _ = r := by ring
  · rw [retaggedAt_tag_of_ne π (J := J) (K := K) (x := x) (hxI := hxI) hKJ]
    exact Metric.mem_closedBall.2 <|
      le_trans (Metric.mem_closedBall.1 (hsub K hK hy)) (by linarith)

/-- Helper for Theorem 4.23: for the Riemann filter, retagging one box by another point of that
box preserves membership in the base set once the common constant radius is doubled. -/
private lemma retaggedAt_memBaseSet_riemann_of_const {ι : Type*} [Fintype ι]
    [DecidableEq (Box ι)] {I : Box ι}
    {c : NNReal} (π : TaggedPrepartition I) {J : Box ι} (hJ : J ∈ π) {r : ℝ} (hr : 0 < r)
    (hr2 : 0 < r / 2)
    (hπ :
      IntegrationParams.Riemann.MemBaseSet I c (fun _ : ι → ℝ ↦ ⟨r / 2, hr2⟩) π)
    {x : ι → ℝ} (hx : x ∈ Box.Icc J) :
    IntegrationParams.Riemann.MemBaseSet I c (fun _ : ι → ℝ ↦ ⟨r, hr⟩)
      (retaggedAt π (J := J) x (Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx)) := by
  let hxI : x ∈ Box.Icc I := Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx
  refine ⟨retaggedAt_isSubordinate_const π hJ hr hr2 hπ.isSubordinate hx hxI, ?_, ?_, ?_⟩
  · intro _ K hK
    by_cases hKJ : K = J
    · subst K
      simpa [retaggedAt_tag_self π (J := J) (x := x) (hxI := hxI)] using hx
    · rw [retaggedAt_tag_of_ne π (J := J) (K := K) (x := x) (hxI := hxI) hKJ]
      exact hπ.isHenstock rfl K hK
  · intro hD
    cases hD
  · intro hD
    cases hD

/-- Helper for Theorem 4.23: retag an entire tagged prepartition while keeping the underlying
prepartition fixed. -/
private def retaggedWith {ι : Type*} [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) (τ : Box ι → ι → ℝ)
    (hτI : ∀ J, τ J ∈ Box.Icc I) :
    TaggedPrepartition I :=
  { toPrepartition := π.toPrepartition
    tag := τ
    tag_mem_Icc := hτI }

/-- Helper for Theorem 4.23: on boxes of the underlying partition, `retaggedWith` uses the new
prescribed tags. -/
private lemma retaggedWith_tag {ι : Type*} [DecidableEq (Box ι)] {I : Box ι}
    (π : TaggedPrepartition I) (τ : Box ι → ι → ℝ)
    (hτI : ∀ J, τ J ∈ Box.Icc I) {J : Box ι} (_hJ : J ∈ π) :
    (retaggedWith π τ hτI).tag J = τ J := by
  rfl

/-- Helper for Theorem 4.23: if a tagged prepartition is subordinate to the constant radius
`r / 2`, then replacing every tag by another point of the same box keeps it subordinate to the
constant radius `r`. -/
private lemma retaggedWith_isSubordinate_const {ι : Type*} [Fintype ι] [DecidableEq (Box ι)]
    {I : Box ι} (π : TaggedPrepartition I) {r : ℝ} (hr : 0 < r) (hr2 : 0 < r / 2)
    (hsub : π.IsSubordinate (fun _ : ι → ℝ ↦ ⟨r / 2, hr2⟩))
    (τ : Box ι → ι → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J)
    (hτI : ∀ J, τ J ∈ Box.Icc I) :
    (retaggedWith π τ hτI).IsSubordinate (fun _ : ι → ℝ ↦ ⟨r, hr⟩) := by
  -- Each retagged box stays inside the old `r / 2`-ball around the old tag, so the new tag is at
  -- distance at most `r / 2` from every point of the box.
  intro J hJ y hy
  rw [retaggedWith_tag π τ hτI hJ, Metric.mem_closedBall]
  have hy' : dist y (π.tag J) ≤ r / 2 := by
    exact Metric.mem_closedBall.1 (hsub J hJ hy)
  have hτ' : dist (π.tag J) (τ J) ≤ r / 2 := by
    simpa [dist_comm] using Metric.mem_closedBall.1 (hsub J hJ (hτ J hJ))
  calc
    dist y (τ J) ≤ dist y (π.tag J) + dist (π.tag J) (τ J) := dist_triangle _ _ _
    _ ≤ r / 2 + r / 2 := add_le_add hy' hτ'
    _ = r := by ring

/-- Helper for Theorem 4.23: for the Riemann filter, whole-partition retagging by points of the
same boxes preserves membership in the base set once the common constant radius is doubled. -/
private lemma retaggedWith_memBaseSet_riemann_of_const {ι : Type*} [Fintype ι]
    [DecidableEq (Box ι)] {I : Box ι} {c : NNReal}
    (π : TaggedPrepartition I) {r : ℝ} (hr : 0 < r) (hr2 : 0 < r / 2)
    (hπ :
      IntegrationParams.Riemann.MemBaseSet I c (fun _ : ι → ℝ ↦ ⟨r / 2, hr2⟩) π)
    (τ : Box ι → ι → ℝ) (hτ : ∀ J ∈ π, τ J ∈ Box.Icc J) (hτI : ∀ J, τ J ∈ Box.Icc I) :
    IntegrationParams.Riemann.MemBaseSet I c (fun _ : ι → ℝ ↦ ⟨r, hr⟩) (retaggedWith π τ hτI) := by
  refine
    ⟨retaggedWith_isSubordinate_const π hr hr2 hπ.isSubordinate τ hτ hτI, ?_, ?_, ?_⟩
  · intro _ J hJ
    simpa [retaggedWith_tag π τ hτI hJ] using hτ J hJ
  · intro hD
    cases hD
  · intro hD
    cases hD

/-- Helper for Theorem 4.23: a common fine Riemann partition controls the single-box variation
term obtained by retagging one box. -/
private lemma single_box_variation_le_of_riemann_partition
    {f : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)}
    (hf :
      Integrable I IntegrationParams.Riemann f volume.toBoxAdditive.toSMul)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ π : TaggedPrepartition I,
      π.IsPartition ∧
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion) π ∧
      ∀ J ∈ π, ∀ x ∈ Box.Icc J,
        ‖volume.toBoxAdditive.toSMul J (f x - f (π.tag J))‖ ≤ ε := by
  classical
  -- Choose one partition subordinate to half of the constant Riemann radius.
  let r : ℝ := hf.convergenceR (ε / 2) I.distortion 0
  have hr : 0 < r := (hf.convergenceR (ε / 2) I.distortion 0).2
  have hr2 : 0 < r / 2 := half_pos hr
  let rhalf : (Fin 1 → ℝ) → Set.Ioi (0 : ℝ) := fun _ ↦ ⟨r / 2, hr2⟩
  obtain ⟨π, hπhalf, hπp⟩ :=
    IntegrationParams.exists_memBaseSet_isPartition IntegrationParams.Riemann I le_rfl rhalf
  have hconst :
      ∀ x : Fin 1 → ℝ,
        hf.convergenceR (ε / 2) I.distortion x = hf.convergenceR (ε / 2) I.distortion 0 := by
    intro x
    exact hf.convergenceR_cond (ε / 2) I.distortion rfl x
  have hπ :
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion) π := by
    -- The half-radius partition is automatically subordinate to the larger convergence radius.
    refine hπhalf.mono (I := I) le_rfl le_rfl ?_
    intro x hx
    rw [hconst x]
    change (r / 2 : ℝ) ≤ r
    linarith
  refine ⟨π, hπp, hπ, ?_⟩
  intro J hJ x hx
  let hxI : x ∈ Box.Icc I := Box.le_iff_Icc.1 (π.le_of_mem' J hJ) hx
  have hπret :
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion)
        (retaggedAt π (J := J) x hxI) := by
    -- Retagging one box stays within the full convergence radius.
    have hπret_half :
        IntegrationParams.Riemann.MemBaseSet I I.distortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩)
          (retaggedAt π (J := J) x hxI) := by
      simpa [r] using
        retaggedAt_memBaseSet_riemann_of_const (π := π) (J := J) hJ hr hr2 hπhalf hx
    refine hπret_half.mono (I := I) le_rfl le_rfl ?_
    intro y hy
    rw [hconst y]
  -- Compare the original and retagged sums through the common Riemann limit.
  have hdist :
      dist (integralSum f volume.toBoxAdditive.toSMul (retaggedAt π (J := J) x hxI))
        (integralSum f volume.toBoxAdditive.toSMul π) ≤ ε := by
    have hhalf : 0 < ε / 2 := half_pos hε
    have :=
      hf.dist_integralSum_le_of_memBaseSet hhalf hhalf hπret hπ rfl
    simpa [add_halves] using this
  -- The difference of the two sums is exactly the single-box variation term.
  rw [dist_eq_norm] at hdist
  simpa [integralSum_retaggedAt_sub_eq π hJ] using hdist

/-- Helper for Theorem 4.23: one-dimensional Riemann box integrability forces a uniform bound on
the lifted integrand over the closed interval box. -/
private lemma boundedOn_realIntervalBox_of_riemannIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    ∃ C : ℝ, ∀ x ∈ Box.Icc (realIntervalBox a b hab), ‖f (x 0)‖ ≤ C := by
  classical
  let I := realIntervalBox a b hab
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ f (x 0)
  obtain ⟨π, hπp, _, hvariation⟩ :=
    single_box_variation_le_of_riemann_partition (I := I) (f := g) hf zero_lt_one
  let boxBound : Box (Fin 1) → ℝ := fun J ↦ ‖g (π.tag J)‖ + (volume.toBoxAdditive J)⁻¹
  let C : ℝ := max ‖f a‖ (∑ J ∈ π.boxes, boxBound J)
  refine ⟨C, ?_⟩
  intro x hx
  by_cases hxa : x 0 = a
  · -- The left endpoint is the only point of `Box.Icc I` not covered by the half-open partition.
    simp [C, hxa]
  · have hxI : x ∈ I := by
      intro i
      fin_cases i
      exact ⟨lt_of_le_of_ne (hx.1 0) (Ne.symm hxa), hx.2 0⟩
    rcases hπp x hxI with ⟨J, hJ, hxJ⟩
    have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
      simp [MeasureTheory.Measure.toBoxAdditive_apply]
    have hvol_eq : volume.toBoxAdditive J = J.upper 0 - J.lower 0 := by
      simpa using (Box.volume_apply J)
    have hvol_pos : 0 < volume.toBoxAdditive J := by
      rw [hvol_eq]
      exact sub_pos.2 (J.lower_lt_upper 0)
    have hmul : volume.toBoxAdditive J * ‖g x - g (π.tag J)‖ ≤ 1 := by
      have hvarJ := hvariation J hJ x (Box.coe_subset_Icc hxJ)
      have hvarJ' : |volume.real (J : Set (Fin 1 → ℝ))| * ‖g x - g (π.tag J)‖ ≤ 1 := by
        simpa [BoxAdditiveMap.toSMul_apply, smul_eq_mul, Real.norm_eq_abs,
          MeasureTheory.Measure.toBoxAdditive_apply] using hvarJ
      simpa [MeasureTheory.Measure.toBoxAdditive_apply, abs_of_nonneg measureReal_nonneg] using
        hvarJ'
    have hdiff : ‖g x - g (π.tag J)‖ ≤ (volume.toBoxAdditive J)⁻¹ := by
      rw [inv_eq_one_div]
      exact (le_div_iff₀ hvol_pos).2 (by simpa [mul_comm] using hmul)
    have hboxBound_nonneg : ∀ K ∈ π.boxes, 0 ≤ boxBound K := by
      intro K hK
      exact add_nonneg (norm_nonneg _) (inv_nonneg.2 (by
        simp [MeasureTheory.Measure.toBoxAdditive_apply]))
    calc
      ‖f (x 0)‖ = ‖g x‖ := rfl
      _ = ‖(g x - g (π.tag J)) + g (π.tag J)‖ := by
        congr 1
        ring
      _ ≤ ‖g x - g (π.tag J)‖ + ‖g (π.tag J)‖ := norm_add_le _ _
      _ ≤ (volume.toBoxAdditive J)⁻¹ + ‖g (π.tag J)‖ := add_le_add hdiff le_rfl
      _ = boxBound J := by rw [add_comm]
      _ ≤ ∑ K ∈ π.boxes, boxBound K := Finset.single_le_sum hboxBound_nonneg hJ
      _ ≤ C := le_max_right _ _

/-- Helper for Theorem 4.23: one common fine Riemann partition controls the integral sums from two
arbitrary boxwise retaggings of that partition. -/
private lemma integralSum_twoRetaggings_le_of_riemannIntegrable
    {g : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)}
    (hf : Integrable I IntegrationParams.Riemann g volume.toBoxAdditive.toSMul)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ π : TaggedPrepartition I,
      π.IsPartition ∧
      IntegrationParams.Riemann.MemBaseSet I I.distortion
        (hf.convergenceR (ε / 2) I.distortion) π ∧
      ∀ τ₁ τ₂ : Box (Fin 1) → Fin 1 → ℝ,
        (∀ J ∈ π, τ₁ J ∈ Box.Icc J) →
        (∀ J ∈ π, τ₂ J ∈ Box.Icc J) →
        (∀ J, τ₁ J ∈ Box.Icc I) →
        (∀ J, τ₂ J ∈ Box.Icc I) →
        ‖∑ J ∈ π.boxes, volume.toBoxAdditive.toSMul J (g (τ₁ J) - g (τ₂ J))‖ ≤ ε := by
  classical
  let r : ℝ := hf.convergenceR (ε / 2) I.distortion 0
  have hr : 0 < r := (hf.convergenceR (ε / 2) I.distortion 0).2
  have hr2 : 0 < r / 2 := half_pos hr
  let rhalf : (Fin 1 → ℝ) → Set.Ioi (0 : ℝ) := fun _ ↦ ⟨r / 2, hr2⟩
  -- Choose one partition subordinate to the half-radius gauge.
  obtain ⟨π, hπhalf, hπp⟩ :=
    IntegrationParams.exists_memBaseSet_isPartition IntegrationParams.Riemann I le_rfl rhalf
  have hconst :
      ∀ x : Fin 1 → ℝ,
        hf.convergenceR (ε / 2) I.distortion x = hf.convergenceR (ε / 2) I.distortion 0 := by
    -- For the Riemann filter, the convergence gauge is constant in the tag.
    intro x
    exact hf.convergenceR_cond (ε / 2) I.distortion rfl x
  refine ⟨π, hπp, ?_, ?_⟩
  · -- The half-radius partition is automatically subordinate to the larger convergence radius.
    refine hπhalf.mono (I := I) le_rfl le_rfl ?_
    intro x hx
    rw [hconst x]
    change (r / 2 : ℝ) ≤ r
    linarith
  · intro τ₁ τ₂ hτ₁ hτ₂ hτ₁I hτ₂I
    let π₁ : TaggedPrepartition I := retaggedWith π τ₁ hτ₁I
    let π₂ : TaggedPrepartition I := retaggedWith π τ₂ hτ₂I
    have hπ₁_const :
        IntegrationParams.Riemann.MemBaseSet I I.distortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) π₁ := by
      -- Retagging inside each box preserves the base-set condition after doubling the radius.
      simpa [π₁] using
        retaggedWith_memBaseSet_riemann_of_const (π := π) hr hr2 hπhalf τ₁ hτ₁ hτ₁I
    have hπ₂_const :
        IntegrationParams.Riemann.MemBaseSet I I.distortion
          (fun _ : Fin 1 → ℝ ↦ ⟨r, hr⟩) π₂ := by
      -- The same transport argument applies to the second retagging.
      simpa [π₂] using
        retaggedWith_memBaseSet_riemann_of_const (π := π) hr hr2 hπhalf τ₂ hτ₂ hτ₂I
    have hπ₁ :
        IntegrationParams.Riemann.MemBaseSet I I.distortion
          (hf.convergenceR (ε / 2) I.distortion) π₁ := by
      refine hπ₁_const.mono (I := I) le_rfl le_rfl ?_
      intro x hx
      rw [hconst x]
    have hπ₂ :
        IntegrationParams.Riemann.MemBaseSet I I.distortion
          (hf.convergenceR (ε / 2) I.distortion) π₂ := by
      refine hπ₂_const.mono (I := I) le_rfl le_rfl ?_
      intro x hx
      rw [hconst x]
    have hUnion : π₁.iUnion = π₂.iUnion := by
      -- Retagging does not change the underlying prepartition, hence the covered set is unchanged.
      simp [π₁, π₂, retaggedWith]
    have hdist :
        dist (integralSum g volume.toBoxAdditive.toSMul π₁)
          (integralSum g volume.toBoxAdditive.toSMul π₂) ≤ ε := by
      have hhalf : 0 < ε / 2 := half_pos hε
      have :=
        hf.dist_integralSum_le_of_memBaseSet hhalf hhalf hπ₁ hπ₂ hUnion
      simpa [add_halves] using this
    rw [dist_eq_norm] at hdist
    have hsum :
        integralSum g volume.toBoxAdditive.toSMul π₁ -
            integralSum g volume.toBoxAdditive.toSMul π₂ =
          ∑ J ∈ π.boxes, volume.toBoxAdditive.toSMul J (g (τ₁ J) - g (τ₂ J)) := by
      -- Expand both integral sums over the same boxes and rewrite each term with `map_sub`.
      unfold integralSum
      rw [show π₁.boxes = π.boxes by rfl, show π₂.boxes = π.boxes by rfl,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl ?_
      intro J hJ
      rw [retaggedWith_tag π τ₁ hτ₁I hJ, retaggedWith_tag π τ₂ hτ₂I hJ]
      simpa using ((volume.toBoxAdditive.toSMul J).map_sub (g (τ₁ J)) (g (τ₂ J))).symm
    rw [← hsum]
    exact hdist

/-- Helper for Theorem 4.23: a point with positive oscillation inside a closed interval box forces
every `nhdsWithin` neighborhood to contain a pair of points with a comparably large value gap. -/
private lemma highOscillation_exists_pair_of_mem_nhdsWithin
    {g : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)} {η : ℝ}
    (hη : 0 < η) {x : Fin 1 → ℝ}
    (hx : ENNReal.ofReal η ≤ oscillationWithin g (Box.Icc I) x) {s : Set (Fin 1 → ℝ)}
    (hs : s ∈ nhdsWithin x (Box.Icc I)) :
    ∃ u ∈ s, ∃ v ∈ s, η / 2 ≤ |g u - g v| := by
  by_contra hpair
  push Not at hpair
  have hsImage : g '' s ∈ (nhdsWithin x (Box.Icc I)).map g := by
    -- The chosen neighborhood contributes one admissible image set in the infimum defining
    -- `oscillationWithin`.
    rw [Filter.mem_map]
    exact Filter.mem_of_superset hs (fun y hy ↦ Set.mem_image_of_mem g hy)
  have hdiam_le : Metric.ediam (g '' s) ≤ ENNReal.ofReal (η / 2) := by
    -- If every pair in `s` has gap `< η / 2`, then the diameter of the image is at most `η / 2`.
    rw [Metric.ediam_image_le_iff]
    intro u hu v hv
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal (le_of_lt <| by
      simpa [Real.dist_eq, Real.norm_eq_abs] using hpair u hu v hv)
  have hosc_le : oscillationWithin g (Box.Icc I) x ≤ ENNReal.ofReal (η / 2) :=
    (biInf_le Metric.ediam hsImage).trans hdiam_le
  have hhalf_lt : ENNReal.ofReal (η / 2) < ENNReal.ofReal η := by
    rw [ENNReal.ofReal_lt_ofReal_iff hη]
    linarith
  -- This contradicts the assumed lower bound on the oscillation at `x`.
  exact (not_lt_of_ge hx) (lt_of_le_of_lt hosc_le hhalf_lt)

/-- Helper for Theorem 4.23: the union of all partition-box boundaries, together with the outer
boundary of the ambient interval box, is null for the restricted volume measure. -/
private lemma measure_partitionBoundary_eq_zero {I : Box (Fin 1)} (π : TaggedPrepartition I) :
    (volume.restrict (Box.Icc I))
      ((⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪
        (Box.Icc I \ Box.Ioo I)) = 0 := by
  have hbox_zero :
      ∀ J ∈ π.boxes, (volume.restrict (Box.Icc I)) (Box.Icc J \ Box.Ioo J) = 0 := by
    intro J hJ
    have hsubset : Box.Icc J \ Box.Ioo J ⊆ Box.Icc I := by
      intro x hx
      exact Box.le_iff_Icc.1 (π.toPrepartition.le_of_mem' J hJ) hx.1
    have hdiff_ae :
        Box.Icc J \ Box.Ioo J =ᵐ[volume] Box.Ioo J \ Box.Ioo J :=
      ae_eq_set_diff (μ := volume) (s := Box.Icc J) (t := Box.Ioo J)
        (s' := Box.Ioo J) (t' := Box.Ioo J) (Box.Ioo_ae_eq_Icc J).symm Filter.EventuallyEq.rfl
    calc
      (volume.restrict (Box.Icc I)) (Box.Icc J \ Box.Ioo J) =
          volume (Box.Icc J \ Box.Ioo J) := Measure.restrict_eq_self volume hsubset
      _ = 0 := by
            refine (measure_congr hdiff_ae).trans ?_
            have hmeasure_empty :
                volume (Box.Ioo J \ Box.Ioo J) = volume (⊥ : Set (Fin 1 → ℝ)) := by
              congr
              ext x
              simp
            exact hmeasure_empty.trans (measure_empty : volume (⊥ : Set (Fin 1 → ℝ)) = 0)
  have hboxes_zero :
      (volume.restrict (Box.Icc I)) (⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) = 0 := by
    have hcount : ((↑π.boxes : Set (Box (Fin 1)))).Countable := Set.to_countable _
    exact (measure_biUnion_null_iff (μ := volume.restrict (Box.Icc I)) hcount).2 hbox_zero
  have hambient_zero :
      (volume.restrict (Box.Icc I)) (Box.Icc I \ Box.Ioo I) = 0 := by
    have hdiff_ae :
        Box.Icc I \ Box.Ioo I =ᵐ[volume] Box.Ioo I \ Box.Ioo I :=
      ae_eq_set_diff (μ := volume) (s := Box.Icc I) (t := Box.Ioo I)
        (s' := Box.Ioo I) (t' := Box.Ioo I)
        (Box.Ioo_ae_eq_Icc I).symm Filter.EventuallyEq.rfl
    calc
      (volume.restrict (Box.Icc I)) (Box.Icc I \ Box.Ioo I) =
          volume (Box.Icc I \ Box.Ioo I) :=
            Measure.restrict_eq_self volume (by intro x hx; exact hx.1)
      _ = 0 := by
            refine (measure_congr hdiff_ae).trans ?_
            have hmeasure_empty :
                volume (Box.Ioo I \ Box.Ioo I) = volume (⊥ : Set (Fin 1 → ℝ)) := by
              congr
              ext x
              simp
            exact hmeasure_empty.trans (measure_empty : volume (⊥ : Set (Fin 1 → ℝ)) = 0)
  -- The total exceptional set is the union of two null pieces.
  exact measure_union_null hboxes_zero hambient_zero

/-- Helper for Theorem 4.23: the strict low-oscillation locus on a closed interval box is open. -/
private lemma isOpen_lowOscillationSet {g : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)} {η : ℝ} :
    IsOpen {y | oscillationWithin g (Box.Icc I) y < ENNReal.ofReal η} := by
  refine EMetric.isOpen_iff.mpr ?_
  intro x hx
  have hx' : oscillationWithin g (Box.Icc I) x < ENNReal.ofReal η := by
    simpa using hx
  obtain ⟨ε, hxε, hεη⟩ := exists_between hx'
  have hsingle :
      ∀ z ∈ ({x} : Set (Fin 1 → ℝ)), oscillationWithin g (Box.Icc I) z < ε := by
    intro z hz
    simpa [Set.mem_singleton_iff.mp hz] using hxε
  have hcompact : IsCompact ({x} : Set (Fin 1 → ℝ)) := isCompact_singleton
  rcases hcompact.uniform_oscillationWithin (D := Box.Icc I) hsingle with ⟨δ, hδ, hδosc⟩
  refine ⟨ENNReal.ofReal (δ / 2), by simpa using ENNReal.ofReal_pos.2 (half_pos hδ), ?_⟩
  intro y hy
  have hy' : edist y x < ENNReal.ofReal (δ / 2) := by
    simpa using hy
  have hball :
      g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ Box.Icc I) ∈
        (nhdsWithin y (Box.Icc I)).map g := by
    rw [Filter.mem_map]
    refine Filter.mem_of_superset
      (inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ (ENNReal.ofReal_pos.2 (half_pos hδ)))) ?_
    intro z hz
    exact Set.mem_image_of_mem g ⟨hz.2, hz.1⟩
  have hsubset :
      Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ Box.Icc I ⊆
        Metric.eball x (ENNReal.ofReal δ) ∩ Box.Icc I := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have htriangle : edist z x ≤ edist z y + edist y x := edist_triangle _ _ _
    have hsum :
        edist z y + edist y x < ENNReal.ofReal δ := by
      have hsum' := ENNReal.add_lt_add hz.1 hy'
      have hadd :
          ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr
        ring
      exact hadd ▸ hsum'
    exact lt_of_le_of_lt htriangle hsum
  have hosc_le :
      oscillationWithin g (Box.Icc I) y ≤
        Metric.ediam (g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ Box.Icc I)) :=
    biInf_le Metric.ediam hball
  have hdiam_le :
      Metric.ediam (g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ Box.Icc I)) ≤ ε := by
    have himage :
        g '' (Metric.eball y (ENNReal.ofReal (δ / 2)) ∩ Box.Icc I) ⊆
          g '' (Metric.eball x (ENNReal.ofReal δ) ∩ Box.Icc I) := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      exact Set.mem_image_of_mem g (hsubset hz)
    exact (Metric.ediam_mono himage).trans (hδosc x (by simp))
  simpa using lt_of_le_of_lt (hosc_le.trans hdiam_le) hεη

/-- Helper for Theorem 4.23: the fixed-threshold high-oscillation set on a closed interval box is
compact. -/
private lemma isCompact_highOscillationSet {g : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)} {η : ℝ} :
    IsCompact {y | y ∈ Box.Icc I ∧ ENNReal.ofReal η ≤ oscillationWithin g (Box.Icc I) y} := by
  have hopen : IsOpen {y | oscillationWithin g (Box.Icc I) y < ENNReal.ofReal η} :=
    isOpen_lowOscillationSet (g := g) (I := I)
  have hrepr :
      {y | y ∈ Box.Icc I ∧ ENNReal.ofReal η ≤ oscillationWithin g (Box.Icc I) y} =
        Box.Icc I \ {y | oscillationWithin g (Box.Icc I) y < ENNReal.ofReal η} := by
    ext y
    simp [not_lt]
  rw [hrepr]
  exact I.isCompact_Icc.of_isClosed_subset
    (I.isCompact_Icc.isClosed.sdiff hopen) Set.diff_subset

/-- Helper for Theorem 4.23: the interior of a one-dimensional box is an open set. -/
private lemma isOpen_boxIoo (J : Box (Fin 1)) : IsOpen (Box.Ioo J) := by
  -- `Box.Ioo J` is a finite-coordinate product of open intervals.
  simpa [BoxIntegral.Box.Ioo] using
    (isOpen_set_pi (i := Set.univ)
      (s := fun i : Fin 1 => Set.Ioo (J.lower i) (J.upper i))
      (Set.toFinite (s := (Set.univ : Set (Fin 1)))) (fun _ _ => isOpen_Ioo))

/-- Helper for Theorem 4.23: every fixed positive high-oscillation set on the closed interval box
has zero restricted volume measure. -/
private lemma measure_highOscillationSet_eq_zero_of_riemannIntegrable
    {g : (Fin 1 → ℝ) → ℝ} {I : Box (Fin 1)}
    (hf : Integrable I IntegrationParams.Riemann g volume.toBoxAdditive.toSMul)
    {η : ℝ} (hη : 0 < η) :
    (volume.restrict (Box.Icc I))
      {y | y ∈ Box.Icc I ∧ ENNReal.ofReal η ≤ oscillationWithin g (Box.Icc I) y} = 0 := by
  classical
  let μI : Measure (Fin 1 → ℝ) := volume.restrict (Box.Icc I)
  let K : Set (Fin 1 → ℝ) :=
    {y | y ∈ Box.Icc I ∧ ENNReal.ofReal η ≤ oscillationWithin g (Box.Icc I) y}
  have hKcompact : IsCompact K := isCompact_highOscillationSet (g := g) (I := I)
  haveI : IsFiniteMeasure μI :=
    { measure_univ_lt_top := by
        simpa [μI, Measure.restrict_apply, I.measurableSet_Icc] using
          I.isCompact_Icc.measure_lt_top (μ := volume) }
  by_cases hK : μI K = 0
  · exact hK
  · have hKpos : 0 < μI K := by
      exact pos_iff_ne_zero.mpr hK
    exfalso
    have hKreal_pos : 0 < μI.real K := ENNReal.toReal_pos hK (measure_lt_top μI K).ne
    obtain ⟨ε, hεpos, hεlt⟩ := exists_between (mul_pos (half_pos hη) hKreal_pos)
    obtain ⟨π, hπp, hπmem, hretag⟩ :=
      integralSum_twoRetaggings_le_of_riemannIntegrable (I := I) (g := g) hf hεpos
    have hπhen : π.IsHenstock := hπmem.isHenstock rfl
    let boundary : Set (Fin 1 → ℝ) :=
      (⋃ J ∈ π.boxes, (Box.Icc J \ Box.Ioo J)) ∪ (Box.Icc I \ Box.Ioo I)
    have hboundary_zero : μI boundary = 0 := by
      simpa [μI, boundary] using measure_partitionBoundary_eq_zero (I := I) π
    let πBad : TaggedPrepartition I :=
      π.filter fun J => ((K \ boundary) ∩ Box.Ioo J).Nonempty
    have hKdiff_subset : K \ boundary ⊆ πBad.iUnion := by
      -- Remove the null boundary set so each remaining bad point lies in the interior of one box.
      intro x hx
      have hxK : x ∈ K := hx.1
      have hxIcc : x ∈ Box.Icc I := hxK.1
      have hxNotBoundary : x ∉ boundary := hx.2
      have hxIooI : x ∈ Box.Ioo I := by
        by_contra hxNotIooI
        exact hxNotBoundary (Or.inr ⟨hxIcc, hxNotIooI⟩)
      have hxI : x ∈ I := I.Ioo_subset_coe hxIooI
      have hπp' : π.toPrepartition.IsPartition := hπp
      rcases ExistsUnique.exists (hπp'.existsUnique hxI) with ⟨J, hJπ, hxJ⟩
      have hxIooJ : x ∈ Box.Ioo J := by
        have hxIccJ : x ∈ Box.Icc J := Box.coe_subset_Icc hxJ
        by_contra hxNotIooJ
        apply hxNotBoundary
        left
        refine Set.mem_iUnion.2 ⟨J, Set.mem_iUnion.2 ⟨hJπ, ?_⟩⟩
        exact ⟨hxIccJ, hxNotIooJ⟩
      have hJbad : J ∈ πBad := by
        exact π.mem_filter.2 ⟨hJπ, ⟨x, ⟨hx, hxIooJ⟩⟩⟩
      exact πBad.subset_iUnion hJbad hxJ
    have hKdiff_pos : 0 < μI (K \ boundary) := by
      rw [measure_diff_null hboundary_zero]
      exact hKpos
    have hKdiff_real : μI.real (K \ boundary) = μI.real K := by
      exact congrArg ENNReal.toReal
        (measure_diff_null (μ := μI) (s := K) (t := boundary) hboundary_zero)
    have hwitness :
        ∀ J ∈ πBad, ∃ u v, u ∈ Box.Ioo J ∧ v ∈ Box.Ioo J ∧ η / 2 ≤ |g u - g v| := by
      intro J hJbad
      rcases (π.mem_filter.1 hJbad).2 with ⟨x, hxKdiff, hxIooJ⟩
      have hsIoo : Box.Ioo J ∈ nhds x := (isOpen_boxIoo J).mem_nhds hxIooJ
      have hs : Box.Ioo J ∈ nhdsWithin x (Box.Icc I) := by
        exact Filter.mem_of_superset (inter_mem_nhdsWithin _ hsIoo) (fun y hy ↦ hy.2)
      have hxOsc : ENNReal.ofReal η ≤ oscillationWithin g (Box.Icc I) x := hxKdiff.1.2
      rcases
        highOscillation_exists_pair_of_mem_nhdsWithin (g := g) (I := I) hη hxOsc hs with
          ⟨u, hu, v, hv, huv⟩
      exact ⟨u, v, hu, hv, huv⟩
    choose u₀ v₀ hu₀ hv₀ hgap using hwitness
    let τLo : Box (Fin 1) → Fin 1 → ℝ := fun J ↦
      if hJ : J ∈ πBad then
        if hle : g (u₀ J hJ) ≤ g (v₀ J hJ) then u₀ J hJ else v₀ J hJ
      else π.tag J
    let τHi : Box (Fin 1) → Fin 1 → ℝ := fun J ↦
      if hJ : J ∈ πBad then
        if hle : g (u₀ J hJ) ≤ g (v₀ J hJ) then v₀ J hJ else u₀ J hJ
      else π.tag J
    have hτLo_box : ∀ J ∈ π, τLo J ∈ Box.Icc J := by
      -- On bad boxes use the chosen witness; elsewhere keep the old Henstock tag.
      intro J hJπ
      by_cases hJbad : J ∈ πBad
      · by_cases hle : g (u₀ J hJbad) ≤ g (v₀ J hJbad)
        · have hmem : u₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hu₀ J hJbad)
          have : u₀ J hJbad ∈ Box.Icc J := hmem
          simpa [τLo, hJbad, hle] using this
        · have hmem : v₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hv₀ J hJbad)
          have : v₀ J hJbad ∈ Box.Icc J := hmem
          simpa [τLo, hJbad, hle] using this
      · simpa [τLo, hJbad] using hπhen J hJπ
    have hτHi_box : ∀ J ∈ π, τHi J ∈ Box.Icc J := by
      -- The second retagging uses the larger-value witness on bad boxes.
      intro J hJπ
      by_cases hJbad : J ∈ πBad
      · by_cases hle : g (u₀ J hJbad) ≤ g (v₀ J hJbad)
        · have hmem : v₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hv₀ J hJbad)
          have : v₀ J hJbad ∈ Box.Icc J := hmem
          simpa [τHi, hJbad, hle] using this
        · have hmem : u₀ J hJbad ∈ Box.Icc J := by
            exact (Box.Ioo_subset_Icc J) (hu₀ J hJbad)
          have : u₀ J hJbad ∈ Box.Icc J := hmem
          simpa [τHi, hJbad, hle] using this
      · simpa [τHi, hJbad] using hπhen J hJπ
    have hτLo_ambient : ∀ J, τLo J ∈ Box.Icc I := by
      -- Every chosen witness still lies in the ambient closed box because its box is a subbox of
      -- the partition.
      intro J
      by_cases hJbad : J ∈ πBad
      · have hJπ : J ∈ π := (π.mem_filter.1 hJbad).1
        have hJI : J ≤ I := π.toPrepartition.le_of_mem' J hJπ
        exact Box.le_iff_Icc.1 hJI (hτLo_box J hJπ)
      · simpa [τLo, hJbad] using π.tag_mem_Icc J
    have hτHi_ambient : ∀ J, τHi J ∈ Box.Icc I := by
      -- The same ambient-box argument applies to the upper retagging.
      intro J
      by_cases hJbad : J ∈ πBad
      · have hJπ : J ∈ π := (π.mem_filter.1 hJbad).1
        have hJI : J ≤ I := π.toPrepartition.le_of_mem' J hJπ
        exact Box.le_iff_Icc.1 hJI (hτHi_box J hJπ)
      · simpa [τHi, hJbad] using π.tag_mem_Icc J
    have hgap_oriented : ∀ J ∈ πBad, η / 2 ≤ g (τHi J) - g (τLo J) := by
      -- Orient the witness pair by value so every bad-box contribution is nonnegative.
      intro J hJbad
      by_cases hle : g (u₀ J hJbad) ≤ g (v₀ J hJbad)
      · have hnonpos : g (u₀ J hJbad) - g (v₀ J hJbad) ≤ 0 := sub_nonpos.mpr hle
        simpa [τLo, τHi, hJbad, hle, abs_of_nonpos hnonpos] using hgap J hJbad
      · have hge : g (v₀ J hJbad) ≤ g (u₀ J hJbad) := le_of_not_ge hle
        simpa [τLo, τHi, hJbad, hle, abs_of_nonneg (sub_nonneg.mpr hge)] using hgap J hJbad
    let term : Box (Fin 1) → ℝ :=
      fun J ↦ volume.toBoxAdditive.toSMul J (g (τHi J) - g (τLo J))
    have hterm_nonneg : ∀ J ∈ π.boxes, 0 ≤ term J := by
      -- Every box contributes a nonnegative amount, and non-bad boxes contribute exactly `0`.
      intro J hJπ
      by_cases hJbad : J ∈ πBad
      · have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
          simp [MeasureTheory.Measure.toBoxAdditive_apply]
        have hgap_nonneg : 0 ≤ g (τHi J) - g (τLo J) := by
          exact le_trans (le_of_lt (half_pos hη)) (hgap_oriented J hJbad)
        simpa [term, BoxAdditiveMap.toSMul_apply, smul_eq_mul] using
          mul_nonneg hvol_nonneg hgap_nonneg
      · simp [term, τLo, τHi, hJbad]
    have hmeasure_selected :
        μI.real πBad.iUnion = ∑ J ∈ πBad.boxes, volume.toBoxAdditive J := by
      -- On every selected box the restricted measure agrees with the ambient volume.
      calc
        μI.real πBad.iUnion = ∑ J ∈ πBad.boxes, μI.real J := by
          simpa [μI] using πBad.toPrepartition.measure_iUnion_toReal (μ := μI)
        _ = ∑ J ∈ πBad.boxes, volume.toBoxAdditive J := by
          refine Finset.sum_congr rfl ?_
          intro J hJ
          have hsubsetJ : (J : Set (Fin 1 → ℝ)) ⊆ Box.Icc I := by
            intro x hx
            exact Box.le_iff_Icc.1 (πBad.toPrepartition.le_of_mem' J hJ) (Box.coe_subset_Icc hx)
          calc
            μI.real J = volume.real (J : Set (Fin 1 → ℝ)) := by
              simp [μI, measureReal_def, Measure.restrict_eq_self volume hsubsetJ]
            _ = volume.toBoxAdditive J := by
              simp [MeasureTheory.Measure.toBoxAdditive_apply]
    have hKdiff_real_le :
        μI.real (K \ boundary) ≤ μI.real πBad.iUnion := by
      exact ENNReal.toReal_mono (measure_lt_top μI _).ne (measure_mono hKdiff_subset)
    have hterm_lower :
        ∀ J ∈ πBad.boxes, (η / 2) * volume.toBoxAdditive J ≤ term J := by
      -- Each selected box contributes at least `(η / 2) * volume(J)`.
      intro J hJ
      have hJbad : J ∈ πBad := hJ
      have hvol_nonneg : 0 ≤ volume.toBoxAdditive J := by
        simp [MeasureTheory.Measure.toBoxAdditive_apply]
      have hmul := mul_le_mul_of_nonneg_left (hgap_oriented J hJbad) hvol_nonneg
      simpa [term, BoxAdditiveMap.toSMul_apply, smul_eq_mul,
        mul_comm, mul_left_comm, mul_assoc] using hmul
    have hsum_selected_le_all :
        ∑ J ∈ πBad.boxes, term J ≤ ∑ J ∈ π.boxes, term J := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun J hJ ↦ (π.mem_filter.1 hJ).1)
        (fun J hJπ hJnot ↦ hterm_nonneg J hJπ)
    have hsum_lower :
        (η / 2) * μI.real K ≤ ∑ J ∈ π.boxes, term J := by
      calc
        (η / 2) * μI.real K = (η / 2) * μI.real (K \ boundary) := by rw [hKdiff_real]
        _ ≤ (η / 2) * μI.real πBad.iUnion := by
          exact mul_le_mul_of_nonneg_left hKdiff_real_le (le_of_lt (half_pos hη))
        _ = ∑ J ∈ πBad.boxes, (η / 2) * volume.toBoxAdditive J := by
          rw [hmeasure_selected, Finset.mul_sum]
        _ ≤ ∑ J ∈ πBad.boxes, term J := Finset.sum_le_sum hterm_lower
        _ ≤ ∑ J ∈ π.boxes, term J := hsum_selected_le_all
    have hsum_bound :
        ‖∑ J ∈ π.boxes, term J‖ ≤ ε := by
      exact hretag τHi τLo hτHi_box hτLo_box hτHi_ambient hτLo_ambient
    have hsum_nonneg : 0 ≤ ∑ J ∈ π.boxes, term J := Finset.sum_nonneg hterm_nonneg
    rw [Real.norm_of_nonneg hsum_nonneg] at hsum_bound
    have hstrict : ε < ∑ J ∈ π.boxes, term J := lt_of_lt_of_le hεlt hsum_lower
    exact (not_lt_of_ge hsum_bound) hstrict

/-- Helper for Theorem 4.23: the remaining structural step is to show that one-dimensional Riemann
box integrability forces `ContinuousWithinAt` almost everywhere on the closed interval box. -/
private lemma aeContinuousWithinAt_realIntervalBox_of_riemannIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    ∀ᵐ x ∂(volume.restrict (Box.Icc (realIntervalBox a b hab))),
      ContinuousWithinAt (fun x : Fin 1 → ℝ ↦ f (x 0))
        (Box.Icc (realIntervalBox a b hab)) x := by
  let I := realIntervalBox a b hab
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ f (x 0)
  let μI : Measure (Fin 1 → ℝ) := volume.restrict (Box.Icc I)
  obtain ⟨C, hC⟩ := boundedOn_realIntervalBox_of_riemannIntegrable hab hf
  have hImageBounded : Bornology.IsBounded (g '' Box.Icc I) := by
    -- The uniform norm bound on the closed box controls the whole image.
    refine (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).2 ?_
    refine ⟨max C 0, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hnorm : ‖g x‖ ≤ max C 0 := le_trans (hC x hx) (le_max_left _ _)
    simpa [Metric.mem_closedBall] using hnorm
  have hosc_ne_top : ∀ x ∈ Box.Icc I, oscillationWithin g (Box.Icc I) x ≠ ⊤ := by
    -- The oscillation is bounded above by the diameter of the bounded image of the whole box.
    intro x hx
    have hsImage : g '' Box.Icc I ∈ (nhdsWithin x (Box.Icc I)).map g := by
      rw [Filter.mem_map]
      exact Filter.mem_of_superset self_mem_nhdsWithin (fun y hy ↦ Set.mem_image_of_mem g hy)
    have hosc_le : oscillationWithin g (Box.Icc I) x ≤ Metric.ediam (g '' Box.Icc I) :=
      biInf_le Metric.ediam hsImage
    exact ne_of_lt (lt_of_le_of_lt hosc_le hImageBounded.ediam_ne_top.lt_top)
  let bad : ℕ → Set (Fin 1 → ℝ) :=
    fun n ↦ {x | x ∈ Box.Icc I ∧
      ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ oscillationWithin g (Box.Icc I) x}
  have hbad_threshold_zero : ∀ n, μI (bad n) = 0 := by
    -- Each fixed threshold is null by the retagging contradiction above.
    intro n
    have hηn : 0 < (1 / (n + 1 : ℝ)) := by positivity
    simpa [μI, bad] using
      measure_highOscillationSet_eq_zero_of_riemannIntegrable (I := I) (g := g) hf hηn
  have hbadUnion_zero : μI (⋃ n, bad n) = 0 := by
    exact measure_iUnion_null (μ := μI) (s := bad) hbad_threshold_zero
  have hbadUnion_ae : ∀ᵐ x ∂μI, x ∉ ⋃ n, bad n := by
    rw [ae_iff]
    have hset : {a | ¬a ∉ ⋃ n, bad n} = ⋃ n, bad n := by
      ext x
      simp
    rw [hset]
    exact hbadUnion_zero
  -- Outside the countable union of null threshold sets, the oscillation must be zero.
  filter_upwards [self_mem_ae_restrict I.measurableSet_Icc, hbadUnion_ae] with x hxI hxBad
  have hosc_zero : oscillationWithin g (Box.Icc I) x = 0 := by
    by_contra hosc
    have hosc_pos : oscillationWithin g (Box.Icc I) x ≠ 0 := hosc
    have hosc_pos_real : 0 < (oscillationWithin g (Box.Icc I) x).toReal :=
      ENNReal.toReal_pos hosc_pos (hosc_ne_top x hxI)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hosc_pos_real
    have hthreshold :
        ENNReal.ofReal (1 / (n + 1 : ℝ)) ≤ oscillationWithin g (Box.Icc I) x := by
      rw [ENNReal.ofReal_le_iff_le_toReal (hosc_ne_top x hxI)]
      exact le_of_lt hn
    have hxBad' : x ∈ ⋃ n, bad n := by
      refine Set.mem_iUnion.2 ⟨n, ?_⟩
      exact ⟨hxI, hthreshold⟩
    exact hxBad hxBad'
  exact (OscillationWithin.eq_zero_iff_continuousWithinAt g hxI).1 hosc_zero

/-- Helper for Theorem 4.23: the structural bridge from one-dimensional Riemann box integrability
to Lebesgue interval integrability and the matching interval-integral value. -/
private lemma riemann_box_intervalIntegrable_and_hasIntegral
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    IntervalIntegrable f volume a b ∧
      HasIntegral (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul (∫ x in a..b, f x ∂volume) := by
  -- Route correction: the failed ambient `AEContinuous` route was too strong, because the
  -- hypothesis only controls `f` on `[a, b]`. The remaining local work is to extract boundedness
  -- and `ContinuousWithinAt` almost everywhere on `Box.Icc (realIntervalBox a b hab)` from the
  -- Riemann filter by retagging a single common fine partition, then pass to the Lebesgue box
  -- integral through `integrable_of_bounded_and_ae_continuousWithinAt`.
  let I := realIntervalBox a b hab
  let g : (Fin 1 → ℝ) → ℝ := fun x ↦ f (x 0)
  have h_bound :
      ∃ C : ℝ, ∀ x ∈ Box.Icc I, ‖g x‖ ≤ C := by
    -- Repackage the existing box bound using the local names `I` and `g`.
    simpa [I, g] using boundedOn_realIntervalBox_of_riemannIntegrable hab hf
  have h_ae_raw :
      ∀ᵐ x ∂(volume.restrict (Box.Icc I)), ContinuousWithinAt g (Box.Icc I) x := by
    -- This is the only remaining structural input from the oscillation argument.
    simpa [I, g] using aeContinuousWithinAt_realIntervalBox_of_riemannIntegrable hab hf
  have h_integrableOn_Icc : IntegrableOn g (Box.Icc I) volume := by
    -- Build Bochner integrability on the closed box from a measurable full-measure continuity set
    -- and the uniform box bound.
    let bad : Set (Fin 1 → ℝ) := {x | ¬ ContinuousWithinAt g (Box.Icc I) x}
    have hbad_zero : volume.restrict (Box.Icc I) bad = 0 := by
      simpa [bad] using (ae_iff.1 h_ae_raw)
    obtain ⟨U, hbadU, hU_meas, hU_zero⟩ := exists_measurable_superset_of_null hbad_zero
    let good : Set (Fin 1 → ℝ) := Box.Icc I \ U
    have hgood_meas : MeasurableSet good := by
      simp [good, hU_meas, I.measurableSet_Icc]
    have hgood_cont : ContinuousOn g good := by
      -- On the measurable full-measure subset `good`, continuity within `Box.Icc I` restricts to
      -- continuity within `good`.
      intro x hx
      have hxcont : ContinuousWithinAt g (Box.Icc I) x := by
        by_contra hxnot
        exact hx.2 (hbadU hxnot)
      exact hxcont.mono <| by
        intro y hy
        exact hy.1
    have hgood_ae : good =ᵐ[volume.restrict (Box.Icc I)] Box.Icc I := by
      have hU_ae : ∀ᵐ x ∂(volume.restrict (Box.Icc I)), x ∉ U := by
        rw [ae_iff]
        simpa using hU_zero
      filter_upwards [self_mem_ae_restrict I.measurableSet_Icc, hU_ae] with x hxI hxU
      apply propext
      constructor
      · intro hx
        exact hx.1
      · intro _
        exact ⟨hxI, hxU⟩
    have h_aestronglyMeasurable : AEStronglyMeasurable g (volume.restrict (Box.Icc I)) := by
      have hrestrict :
          (volume.restrict (Box.Icc I)).restrict good =
            (volume.restrict (Box.Icc I)).restrict (Box.Icc I) :=
        Measure.restrict_congr_set hgood_ae
      have hgood_aemeasurable :
          AEMeasurable g ((volume.restrict (Box.Icc I)).restrict good) :=
        hgood_cont.aemeasurable (μ := volume.restrict (Box.Icc I)) hgood_meas
      rw [hrestrict] at hgood_aemeasurable
      have hgood_aemeasurable' : AEMeasurable g (volume.restrict (Box.Icc I)) := by
        simpa [Measure.restrict_restrict, I.measurableSet_Icc] using hgood_aemeasurable
      exact hgood_aemeasurable'.aestronglyMeasurable
    have h_hasFiniteIntegral : HasFiniteIntegral g (volume.restrict (Box.Icc I)) := by
      have : IsFiniteMeasure (volume.restrict (Box.Icc I)) :=
        { measure_univ_lt_top := by simpa using I.isCompact_Icc.measure_lt_top (μ := volume) }
      obtain ⟨C, hC⟩ := h_bound
      refine HasFiniteIntegral.of_bounded (C := C) ?_
      filter_upwards [self_mem_ae_restrict I.measurableSet_Icc] with x hx
      exact hC x hx
    exact ⟨h_aestronglyMeasurable, h_hasFiniteIntegral⟩
  have h_I_ae_Icc : (I : Set (Fin 1 → ℝ)) =ᵐ[volume] Box.Icc I := by
    -- In one dimension the half-open box and its closed hull differ only at the left endpoint.
    have hpi :
        (I : Set (Fin 1 → ℝ)) =
          Set.univ.pi fun i : Fin 1 ↦ Set.Ioc ((![a] : Fin 1 → ℝ) i) ((![b] : Fin 1 → ℝ) i) := by
      simp [I, realIntervalBox, Box.coe_eq_pi]
    rw [hpi]
    simpa [I, realIntervalBox_Icc_eq, MeasureTheory.volume_pi] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (μ := fun _ : Fin 1 ↦ (volume : Measure ℝ))
        (f := ![a]) (g := ![b]))
  have h_integrableOn_I : IntegrableOn g I volume :=
    h_integrableOn_Icc.congr_set_ae h_I_ae_Icc
  have h_integrableOn_realIoc : IntegrableOn f (Set.Ioc a b) volume := by
    -- Transport the half-open box integrability back to the real interval.
    have h_integrableOn_pi : IntegrableOn g (Set.Ioc ![a] ![b]) volume := by
      simpa [I, g, realIntervalBox_coe_eq] using h_integrableOn_I
    simpa [g] using
      (integrableOn_Ioc_funUnique_iff (f := f) (a := a) (b := b)).1 h_integrableOn_pi
  have h_interval : IntervalIntegrable f volume a b := by
    -- Interval integrability is exactly integrability on `(a, b]` for `a ≤ b`.
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    exact h_integrableOn_realIoc
  have h_henstock_set :
      HasIntegral I IntegrationParams.Henstock g volume.toBoxAdditive.toSMul
        (∫ x in I, g x ∂volume) :=
    IntegrableOn.hasBoxIntegral h_integrableOn_I IntegrationParams.Henstock rfl
  have h_henstock_riemannValue :
      HasIntegral I IntegrationParams.Henstock g volume.toBoxAdditive.toSMul
        (integral I IntegrationParams.Riemann g volume.toBoxAdditive.toSMul) :=
    (hf.hasIntegral).mono BoxIntegral.IntegrationParams.henstock_le_riemann
  have h_value_eq :
      integral I IntegrationParams.Riemann g volume.toBoxAdditive.toSMul =
        ∫ x in a..b, f x ∂volume := by
    -- Uniqueness for the Henstock integral identifies the Riemann box integral with the set
    -- integral on the half-open box, then the `Fin 1` model collapses to the real interval.
    calc
      integral I IntegrationParams.Riemann g volume.toBoxAdditive.toSMul =
          ∫ x in I, g x ∂volume :=
        HasIntegral.unique h_henstock_riemannValue h_henstock_set
      _ = ∫ x in Set.Ioc a b, f x ∂volume := by
        simpa [I, g, realIntervalBox_coe_eq] using
          (setIntegral_Ioc_funUnique_eq (f := f) (a := a) (b := b))
      _ = ∫ x in a..b, f x ∂volume := (intervalIntegral.integral_of_le hab.le).symm
  refine ⟨h_interval, ?_⟩
  -- Rewrite the value supplied by `hf.hasIntegral` using the Henstock/Lebesgue comparison above.
  simpa [I, g, h_value_eq] using hf.hasIntegral

-- Proof sketch: transport the Riemann-style `BoxIntegral.Integrable` hypothesis on the
-- one-dimensional box to a Lebesgue `IntervalIntegrable` statement on `a..b`, then identify the
-- resulting box integral with the interval integral.
/-- Theorem 4.23: if `f` is Riemann integrable on `[a,b]`, encoded here as Riemann box
integrability of `fun x ↦ f (x 0)` on the one-dimensional box attached to `(a,b]`, then `f` is
Lebesgue integrable on `a..b`, and the interval integral equals the Riemann integral. -/
theorem intervalIntegrable_and_intervalIntegral_eq_of_riemannIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    IntervalIntegrable f volume a b ∧
      ∫ x in a..b, f x ∂volume =
        integral (realIntervalBox a b hab) IntegrationParams.Riemann
          (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := by
  -- Route correction: isolate the missing Riemann-to-Lebesgue bridge in one helper, then the main
  -- theorem closes by reading off interval integrability and the box-integral value.
  rcases riemann_box_intervalIntegrable_and_hasIntegral hab hf with ⟨hf_interval, hf_hasIntegral⟩
  refine ⟨hf_interval, ?_⟩
  -- Once the helper supplies the matching box integral, the numerical identity is immediate.
  exact hf_hasIntegral.integral_eq.symm

/-- Companion bridge for Theorem 4.23 in `Set.Icc` form. -/
theorem integrableOn_Icc_and_integral_eq_of_riemannIntegrable
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf :
      Integrable (realIntervalBox a b hab) IntegrationParams.Riemann
        (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul) :
    IntegrableOn f (Set.Icc a b) volume ∧
      ∫ x in Set.Icc a b, f x ∂volume =
        integral (realIntervalBox a b hab) IntegrationParams.Riemann
          (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := by
  rcases intervalIntegrable_and_intervalIntegral_eq_of_riemannIntegrable hab hf with
    ⟨hf_interval, h_integral_eq⟩
  have hf_Icc : IntegrableOn f (Set.Icc a b) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hf_interval
  refine ⟨hf_Icc, ?_⟩
  calc
    ∫ x in Set.Icc a b, f x ∂volume =
        ∫ x in Set.Ioc a b, f x ∂volume := integral_Icc_eq_integral_Ioc
    _ = ∫ x in a..b, f x ∂volume := (integral_of_le hab.le).symm
    _ = integral (realIntervalBox a b hab) IntegrationParams.Riemann
          (fun x ↦ f (x 0)) volume.toBoxAdditive.toSMul := h_integral_eq

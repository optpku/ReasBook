/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Theorem_8_15
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

open scoped ContDiff

namespace BVCompactness

/-- Helper for Theorem 8.16: transport the Fréchet derivative of a smooth scalar to the Euclidean
gradient vector by the Riesz isometry. -/
lemma smoothCompactSupport_rieszGradientContinuous
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ_smooth : ContDiff ℝ 1 φ) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)) := by
  -- Differentiate once, then transport the derivative through the inverse Riesz map.
  exact
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.continuous.comp
      (hφ_smooth.continuous_fderiv (by norm_num))

/-- Helper for Theorem 8.16: the Euclidean gradient field of a compactly supported smooth scalar
has compact support. -/
lemma smoothCompactSupport_rieszGradientHasCompactSupport
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ_compact : HasCompactSupport φ) :
    HasCompactSupport
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)) := by
  -- The derivative already has compact support; composing with the inverse Riesz map preserves it.
  exact
    (hφ_compact.fderiv ℝ).comp_left
      (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm) (by simp)

/-- Helper for Theorem 8.16: the Euclidean gradient field of a compactly supported smooth scalar
belongs to `L¹(domainMeasure Ω)`. -/
lemma smoothCompactSupport_rieszGradientMemLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ_smooth : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ) :
    MeasureTheory.MemLp
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x))
      1 (domainMeasure Ω) := by
  -- Continuity plus compact support is the canonical `L¹` bridge on the domain measure.
  exact
    (smoothCompactSupport_rieszGradientContinuous (Ω := Ω) hφ_smooth).memLp_of_hasCompactSupport
      (μ := domainMeasure Ω)
      (smoothCompactSupport_rieszGradientHasCompactSupport (Ω := Ω) hφ_compact)

/-- Helper for Theorem 8.16: the Riesz-transported Euclidean gradient has the same pointwise norm
as the Fréchet derivative. -/
lemma integral_norm_rieszGradient_eq_integral_norm_fderiv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} :
    ∫ x,
        ‖(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)‖
        ∂domainMeasure Ω =
      ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω := by
  -- The inverse Riesz map is an isometry, so the two integrands agree pointwise.
  refine MeasureTheory.integral_congr_ae ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    simpa using
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm.norm_map
        (fderiv ℝ φ x)

/-- Helper for Theorem 8.16: each coordinate summand in the raw divergence of a `C¹` field is
continuous. -/
lemma rawDivergenceSummandContinuous
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_cont : ContDiff ℝ 1 φ)
    (i : Fin d) :
    Continuous
      (fun x ↦
        (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) := by
  -- Keep the derivative evaluation in the `PiLp` normal form that Lean already uses for
  -- Euclidean coordinates, then project to one scalar coordinate.
  have hderiv :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          fderiv ℝ φ x (PiLp.single 2 i (1 : ℝ))) := by
    have happly :
        Continuous
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
            (fderiv ℝ φ p.1) p.2) :=
      hφ_cont.continuous_fderiv_apply (by norm_num)
    -- Freeze the basis direction before projecting to a scalar coordinate.
    have hfreeze :
        Continuous
          (fun x : EuclideanSpace ℝ (Fin d) ↦
            (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin d) ↦
              (fderiv ℝ φ p.1) p.2)
              (x, WithLp.toLp 2 (Pi.single i (1 : ℝ)))) :=
      happly.comp (continuous_id.prodMk continuous_const)
    simpa [PiLp.toLp_single] using hfreeze
  have happly :
      Continuous (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i) :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin d => ℝ) i
  have hcoord :
      Continuous
        (fun x : EuclideanSpace ℝ (Fin d) ↦
          (fun y : EuclideanSpace ℝ (Fin d) ↦ y.ofLp i)
            (fderiv ℝ φ x (PiLp.single 2 i (1 : ℝ)))) :=
    happly.comp hderiv
  simpa using hcoord

/-- Helper for Theorem 8.16: the raw divergence of a `C¹` field is continuous. -/
lemma rawDivergenceContinuous
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    (hφ_cont : ContDiff ℝ 1 φ) :
    Continuous
      (fun x : EuclideanSpace ℝ (Fin d) ↦
        ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) := by
  -- Sum the coordinate continuity lemmas in the source-facing divergence spelling.
  exact continuous_finsetSum Finset.univ fun i _ ↦
    rawDivergenceSummandContinuous hφ_cont i

/-- Helper for Theorem 8.16: the raw divergence of a field vanishes away from the topological
support of that field. -/
lemma rawDivergence_eq_zero_of_notMem_tsupport
    {φ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ tsupport φ) :
    (∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) i) = 0 := by
  -- Each coordinate derivative vanishes once the field is locally zero.
  simp [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]

/-- Helper for Theorem 8.16: a compactly supported ambient `C¹` field on Euclidean space has
zero total raw divergence against volume. -/
lemma compactlySupported_divergence_eq_zero_volume
    {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hφ_cont : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ) :
    ∫ x,
        (∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂(MeasureTheory.volume) = 0 := by
  let divφ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x ↦
    ∑ i : Fin (n + 1), fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) i
  have hdiv_cont : Continuous divφ := by
    -- The raw divergence stays continuous because `φ` is `C¹`.
    simpa [divφ] using rawDivergenceContinuous hφ_cont
  have hdiv_support_subset : Function.support divφ ⊆ tsupport φ := by
    -- Outside the topological support of `φ`, every divergence summand vanishes.
    intro x hx
    by_contra hxφ
    exact hx <| by
      simpa [divφ] using rawDivergence_eq_zero_of_notMem_tsupport (φ := φ) hxφ
  have hdiv_tsupport_subset_tsupport : tsupport divφ ⊆ tsupport φ := by
    -- Passing from support to topological support is safe because `tsupport φ` is closed.
    simpa [tsupport] using closure_minimal hdiv_support_subset (isClosed_tsupport φ)
  obtain ⟨R₀, htsupport_ball₀⟩ :=
    hφ_compact.isCompact.isBounded.subset_ball (0 : EuclideanSpace ℝ (Fin (n + 1)))
  let R : ℝ := max R₀ 1
  have hR_pos : 0 < R := by
    -- Enlarge the bounding radius to a strictly positive one so the comparison cube has interior.
    dsimp [R]
    positivity
  have htsupport_ball :
      tsupport φ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R := by
    -- The compact support sits in a slightly larger open ball.
    intro x hx
    exact Metric.ball_subset_ball (le_max_left _ _) (htsupport_ball₀ hx)
  let eL : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] (Fin (n + 1) → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)
  -- Local instance justification (order transport): the box divergence theorem is stated for
  -- ordered ambient spaces, and the only natural order here is the coordinatewise order
  -- transported through `EuclideanSpace.equiv`.
  letI : Preorder (EuclideanSpace ℝ (Fin (n + 1))) := Preorder.lift eL
  let a : EuclideanSpace ℝ (Fin (n + 1)) :=
    show EuclideanSpace ℝ (Fin (n + 1)) from
      WithLp.toLp 2 (fun _ : Fin (n + 1) ↦ -R)
  let b : EuclideanSpace ℝ (Fin (n + 1)) :=
    show EuclideanSpace ℝ (Fin (n + 1)) from
      WithLp.toLp 2 (fun _ : Fin (n + 1) ↦ R)
  have hab : a ≤ b := by
    intro i
    change eL a i ≤ eL b i
    simp [eL, a, b, hR_pos.le]
  have hball_subset_box :
      Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R ⊆ Set.Icc a b := by
    -- A point of norm `< R` has every coordinate between `-R` and `R`.
    intro x hx
    constructor
    · intro i
      have hcoord :
          |x i| < R := by
        calc
          |x i| = ‖x i‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x‖ := PiLp.norm_apply_le x i
          _ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx
      have hcoord' := (abs_lt.mp hcoord).1
      change eL a i ≤ eL x i
      exact le_of_lt (by simpa [eL, a] using hcoord')
    · intro i
      have hcoord :
          |x i| < R := by
        calc
          |x i| = ‖x i‖ := by rw [Real.norm_eq_abs]
          _ ≤ ‖x‖ := PiLp.norm_apply_le x i
          _ < R := by simpa [Metric.mem_ball, dist_zero_right] using hx
      have hcoord' := (abs_lt.mp hcoord).2
      change eL x i ≤ eL b i
      exact le_of_lt (by simpa [eL, b] using hcoord')
  have hdiv_zero_outsideBox : ∀ x ∉ Set.Icc a b, divφ x = 0 := by
    -- The divergence vanishes outside the enclosing cube because `φ` itself does.
    intro x hxBox
    exact image_eq_zero_of_notMem_tsupport <| fun hxdiv ↦
      hxBox (hball_subset_box (htsupport_ball (hdiv_tsupport_subset_tsupport hxdiv)))
  let coord : Fin (n + 1) → EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun i x ↦ φ x i
  let coordDeriv :
      Fin (n + 1) →
        EuclideanSpace ℝ (Fin (n + 1)) →
          EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ :=
    fun i x ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).comp (fderiv ℝ φ x)
  have hIcc_compact : IsCompact (Set.Icc a b) := by
    have hpre : Set.Icc a b = eL ⁻¹' Set.Icc (eL a) (eL b) := by
      ext x
      change (a ≤ x ∧ x ≤ b) ↔ (eL a ≤ eL x ∧ eL x ≤ eL b)
      rfl
    rw [hpre]
    exact (eL.toHomeomorph.isCompact_preimage).2
      (isCompact_Icc : IsCompact (Set.Icc (eL a) (eL b)))
  have hbox_integral :
      ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume) = 0 := by
    have hcube :
        ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume) =
          ∑ i : Fin (n + 1),
            ((∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL b i) x) ∂MeasureTheory.volume) -
              ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL a i) x) ∂MeasureTheory.volume) := by
      -- Transport the field to coordinate space and apply the box divergence theorem there.
      refine MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable_of_equiv
        eL (fun _ _ ↦ by rfl)
        (by
          change MeasureTheory.MeasurePreserving
            (@WithLp.ofLp 2 (Fin (n + 1) → ℝ))
          exact PiLp.volume_preserving_ofLp (Fin (n + 1)))
        coord coordDeriv ∅ (by simpa) a b hab ?_ ?_ divφ ?_ ?_
      · intro i
        exact ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hφ_cont.continuous).continuousOn
      · intro x _ i
        -- Differentiate the `i`th coordinate by composing with the continuous linear projection.
        exact ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
          ((hφ_cont.differentiable_one x).hasFDerivAt))
      · intro x
        -- This identifies the theorem's packaged divergence with the source-facing raw divergence.
        simp [divφ, coordDeriv, eL, EuclideanSpace.coe_proj, PiLp.toLp_single]
      · -- Continuity on the compact cube gives integrability of the divergence there.
        exact hdiv_cont.continuousOn.integrableOn_compact hIcc_compact
    have hfront_zero :
        ∀ i : Fin (n + 1),
          ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            coord i (eL.symm <| i.insertNth (eL b i) x) ∂MeasureTheory.volume = 0 := by
      intro i
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      have hy_norm :
          R ≤ ‖eL.symm <| i.insertNth (eL b i) x‖ := by
        calc
          R = ‖(eL.symm <| i.insertNth (eL b i) x) i‖ := by
            rw [Real.norm_eq_abs]
            simpa [abs_of_nonneg hR_pos.le, eL, b]
          _ ≤ ‖eL.symm <| i.insertNth (eL b i) x‖ := PiLp.norm_apply_le _ i
      have hy_not_mem : eL.symm (i.insertNth (eL b i) x) ∉ tsupport φ := by
        intro hy_mem
        have hy_ball : eL.symm (i.insertNth (eL b i) x) ∈
            Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R :=
          htsupport_ball hy_mem
        exact (not_lt_of_ge hy_norm) <| by
          simpa [Metric.mem_ball, dist_zero_right] using hy_ball
      -- The field vanishes on every front face because the whole support lies strictly inside the cube.
      simpa [coord] using
        congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i)
          (image_eq_zero_of_notMem_tsupport hy_not_mem)
    have hback_zero :
        ∀ i : Fin (n + 1),
          ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
            coord i (eL.symm <| i.insertNth (eL a i) x) ∂MeasureTheory.volume = 0 := by
      intro i
      refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero ?_
      intro x hx
      have hy_norm :
          R ≤ ‖eL.symm <| i.insertNth (eL a i) x‖ := by
        calc
          R = ‖(eL.symm <| i.insertNth (eL a i) x) i‖ := by
            rw [Real.norm_eq_abs]
            simpa [abs_of_nonneg hR_pos.le, eL, a]
          _ ≤ ‖eL.symm <| i.insertNth (eL a i) x‖ := PiLp.norm_apply_le _ i
      have hy_not_mem : eL.symm (i.insertNth (eL a i) x) ∉ tsupport φ := by
        intro hy_mem
        have hy_ball : eL.symm (i.insertNth (eL a i) x) ∈
            Metric.ball (0 : EuclideanSpace ℝ (Fin (n + 1))) R :=
          htsupport_ball hy_mem
        exact (not_lt_of_ge hy_norm) <| by
          simpa [Metric.mem_ball, dist_zero_right] using hy_ball
      -- The same support argument kills every back-face contribution.
      simpa [coord] using
        congrArg (fun z : EuclideanSpace ℝ (Fin (n + 1)) => z i)
          (image_eq_zero_of_notMem_tsupport hy_not_mem)
    calc
      ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume)
        = ∑ i : Fin (n + 1),
            ((∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL b i) x) ∂MeasureTheory.volume) -
              ∫ x in Set.Icc (eL a ∘ i.succAbove) (eL b ∘ i.succAbove),
                coord i (eL.symm <| i.insertNth (eL a i) x) ∂MeasureTheory.volume) := hcube
      _ = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        simp [hfront_zero i, hback_zero i]
  -- Isolate the Euclidean transport once in this whole-space helper so later supported
  -- `W¹,¹` arguments can call it without rebuilding the box argument.
  calc
    ∫ x, divφ x ∂(MeasureTheory.volume) = ∫ x in Set.Icc a b, divφ x ∂(MeasureTheory.volume) := by
      symm
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hdiv_zero_outsideBox
    _ = 0 := hbox_integral

/-- Helper for Theorem 8.16: a compactly supported ambient `C¹` field on `Fin d` has zero raw
divergence integral against volume. -/
lemma compactlySupported_divergence_eq_zero_volume_fin
    (ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hψ_cont : ContDiff ℝ 1 ψ)
    (hψ_compact : HasCompactSupport ψ) :
    ∫ x,
        (∑ i : Fin d, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i)
        ∂MeasureTheory.volume = 0 := by
  cases d with
  | zero =>
      simp
  | succ n =>
      simpa using
        compactlySupported_divergence_eq_zero_volume (n := n) ψ hψ_cont hψ_compact

/-- Helper for Theorem 8.16: a smooth scalar with compact support inside `Ω` packages as a
`W¹,¹(Ω)` element whose weak-gradient norm integral is exactly the integral of the Fréchet
derivative norm. -/
lemma smoothCompactSupport_memW11
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ_smooth : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subset : tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ w : W¹,¹(Ω),
      w.toL1 =
        MeasureTheory.MemLp.toLp φ
          (hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact) ∧
      ∫ x, ‖w.weakGradient x‖ ∂domainMeasure Ω =
        ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω := by
  let toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
    MeasureTheory.MemLp.toLp φ
      (hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact)
  let grad :
      EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x ↦ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).symm (fderiv ℝ φ x)
  have hgradMem :
      MeasureTheory.MemLp grad 1 (domainMeasure Ω) := by
    -- The Riesz-transported gradient is an `L¹` field by continuity and compact support.
    simpa [grad] using
      smoothCompactSupport_rieszGradientMemLp (Ω := Ω) hφ_smooth hφ_compact
  let weakGradient : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω) :=
    MeasureTheory.MemLp.toLp grad hgradMem
  have hPairing :
      ∀ v : AdmissibleTestField Ω,
        admissibleDivergencePairing toL1 v =
          -∫ x, inner ℝ (weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω := by
    intro v
    let ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
      fun x ↦ φ x • v.toTestFunction x
    let divψ : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦
      ∑ i : Fin d, fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i
    have hψ_smooth : ContDiff ℝ 1 ψ := by
      -- The product field is `C¹` because both the scalar and vector factors are smooth.
      change ContDiff ℝ 1 (φ • ⇑v.toTestFunction)
      simpa [ψ] using hφ_smooth.smul v.toTestFunction.contDiff
    have hψ_compact : HasCompactSupport ψ := by
      -- Compact support is inherited from the scalar factor.
      change HasCompactSupport (φ • ⇑v.toTestFunction)
      simpa [ψ] using hφ_compact.smul_right (f' := v.toTestFunction)
    have hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
      -- The product field still vanishes outside `Ω`.
      simpa [ψ] using (tsupport_smul_subset_left φ v.toTestFunction).trans hφ_subset
    have hdivψ_zero :
        ∫ x, divψ x ∂domainMeasure Ω = 0 := by
      -- The raw divergence vanishes off `Ω`, so the domain integral reduces to the ambient
      -- whole-space divergence theorem for compactly supported `C¹` fields.
      rw [domainMeasure_def, EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
      change ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))), divψ x ∂MeasureTheory.volume = 0
      calc
        ∫ x in (Ω : Set (EuclideanSpace ℝ (Fin d))), divψ x ∂MeasureTheory.volume
            = ∫ x, divψ x ∂MeasureTheory.volume := by
                refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero ?_
                intro x hxΩ
                exact rawDivergence_eq_zero_of_notMem_tsupport (φ := ψ) fun hxψ ↦ hxΩ (hψ_subset hxψ)
        _ = 0 := by
              simpa [divψ] using
                compactlySupported_divergence_eq_zero_volume_fin (d := d) ψ hψ_smooth hψ_compact
    have hdivψ_formula :
        ∀ x,
          divψ x =
            inner ℝ (grad x) (v.toTestFunction x) + φ x * admissibleDivergence v x := by
      intro x
      have hsum :
          ∀ i : Fin d,
            fderiv ℝ ψ x (EuclideanSpace.single i (1 : ℝ)) i =
              (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) * v.toTestFunction x i +
                φ x * fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i := by
        intro i
        have hfd :
            fderiv ℝ ψ x =
              φ x • fderiv ℝ v.toTestFunction x + (fderiv ℝ φ x).smulRight (v.toTestFunction x) := by
          change
            fderiv ℝ (φ • ⇑v.toTestFunction) x =
              φ x • fderiv ℝ (⇑v.toTestFunction) x + (fderiv ℝ φ x).smulRight (v.toTestFunction x)
          simpa [add_comm] using
            fderiv_smul (c := φ) (f := v.toTestFunction)
              (hφ_smooth.contDiffAt.differentiableAt (by norm_num))
              (v.toTestFunction.contDiff.contDiffAt.differentiableAt (by norm_num))
        have happly :=
          congrArg
            (fun L : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) ↦
              L (EuclideanSpace.single i (1 : ℝ)) i)
            hfd
        calc
          ((fderiv ℝ ψ x) (EuclideanSpace.single i (1 : ℝ))) i
              = φ x * ((fderiv ℝ (⇑v.toTestFunction) x) (EuclideanSpace.single i (1 : ℝ))) i +
                  (v.toTestFunction x) i * (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := by
                    simpa [add_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
                      mul_comm, mul_left_comm, mul_assoc] using happly
          _ = (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) * v.toTestFunction x i +
                φ x * fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i := by
                ring
      have hinner_eval :
          inner ℝ (grad x) (v.toTestFunction x) =
            ∑ i : Fin d,
              (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) * v.toTestFunction x i := by
        have hsum_repr :
            ∑ i : Fin d, v.toTestFunction x i • EuclideanSpace.single i (1 : ℝ) =
              v.toTestFunction x := by
          simpa using
            (EuclideanSpace.basisFun (ι := Fin d) ℝ).sum_repr (v.toTestFunction x)
        calc
          inner ℝ (grad x) (v.toTestFunction x)
              = (fderiv ℝ φ x) (v.toTestFunction x) := by
                  simpa [grad] using
                    (InnerProductSpace.toDual_symm_apply
                      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d))
                      (x := v.toTestFunction x) (y := fderiv ℝ φ x))
          _ = (fderiv ℝ φ x) (∑ i : Fin d, v.toTestFunction x i • EuclideanSpace.single i (1 : ℝ)) := by
                rw [hsum_repr]
          _ = ∑ i : Fin d, (fderiv ℝ φ x) (v.toTestFunction x i • EuclideanSpace.single i (1 : ℝ)) := by
                rw [map_sum]
          _ = ∑ i : Fin d, (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) * v.toTestFunction x i := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [map_smul]
                ring
      calc
        divψ x = ∑ i : Fin d,
            ((fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) * v.toTestFunction x i +
              φ x * fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i) := by
                unfold divψ
                refine Finset.sum_congr rfl ?_
                intro i hi
                exact hsum i
        _ = (∑ i : Fin d,
            (fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) * v.toTestFunction x i) +
              ∑ i : Fin d, φ x * fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i := by
                rw [Finset.sum_add_distrib]
        _ = inner ℝ (grad x) (v.toTestFunction x) + φ x * admissibleDivergence v x := by
              rw [hinner_eval, admissibleDivergence_def]
              simp [Finset.mul_sum, add_comm, add_left_comm, add_assoc]
    have hpairInt :
        MeasureTheory.Integrable
          (fun x ↦ φ x * admissibleDivergence v x) (domainMeasure Ω) := by
      -- The scalar pairing density is continuous and compactly supported.
      have hcont :
          Continuous (fun x ↦ φ x * admissibleDivergence v x) :=
        hφ_smooth.continuous.mul (admissibleDivergenceContinuous v)
      have hcompact :
          HasCompactSupport (fun x ↦ φ x * admissibleDivergence v x) :=
        hφ_compact.mul_right
      simpa [MeasureTheory.memLp_one_iff_integrable] using
        (hcont.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hcompact :
          MeasureTheory.MemLp (fun x ↦ φ x * admissibleDivergence v x) 1 (domainMeasure Ω))
    have hgradInt :
        MeasureTheory.Integrable grad (domainMeasure Ω) := by
      -- The vector gradient is in `L¹(domainMeasure Ω)` by the previous helper.
      simpa [MeasureTheory.memLp_one_iff_integrable] using hgradMem
    have hinnerInt :
        MeasureTheory.Integrable
          (fun x ↦ inner ℝ (grad x) (v.toTestFunction x)) (domainMeasure Ω) := by
      -- Reuse the Chapter 8 admissible-pairing integrability bridge for vector fields.
      exact
        (integrableNegInner_of_admissible (Ω := Ω) (g := grad) hgradInt v).neg.congr
          (Filter.Eventually.of_forall fun x ↦ by simp)
    have hdivψ_integral :
        ∫ x, inner ℝ (grad x) (v.toTestFunction x) + φ x * admissibleDivergence v x
            ∂domainMeasure Ω = 0 := by
      -- Rewrite the divergence integrand pointwise to the weak-gradient and pairing densities.
      calc
        ∫ x, inner ℝ (grad x) (v.toTestFunction x) + φ x * admissibleDivergence v x
            ∂domainMeasure Ω
            = ∫ x, divψ x ∂domainMeasure Ω := by
                refine MeasureTheory.integral_congr_ae ?_
                exact Filter.Eventually.of_forall fun x ↦ (hdivψ_formula x).symm
        _ = 0 := hdivψ_zero
    have hpair_repr :
        admissibleDivergencePairing toL1 v =
          ∫ x, φ x * admissibleDivergence v x ∂domainMeasure Ω := by
      -- The `L¹` representative stored in `toL1` is exactly the original scalar function `φ`.
      rw [admissibleDivergencePairing_def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards
        [MeasureTheory.MemLp.coeFn_toLp
          (hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact)] with x hx
      rw [hx]
    have hweak_repr :
        ∫ x, inner ℝ (weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω =
          ∫ x, inner ℝ (grad x) (v.toTestFunction x) ∂domainMeasure Ω := by
      -- The stored weak gradient in `weakGradient` is the original vector field `grad`.
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.MemLp.coeFn_toLp hgradMem] with x hx
      rw [hx]
    have hsum_zero :
        ∫ x, inner ℝ (grad x) (v.toTestFunction x) ∂domainMeasure Ω +
            admissibleDivergencePairing toL1 v = 0 := by
      -- Separate the two integrable summands and rewrite the scalar pairing term.
      rw [hpair_repr, ← MeasureTheory.integral_add hinnerInt hpairInt]
      exact hdivψ_integral
    have hsum_zero' :
        ∫ x, inner ℝ (weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω +
            admissibleDivergencePairing toL1 v = 0 := by
      rw [hweak_repr]
      exact hsum_zero
    linarith
  refine ⟨W11.ofLp toL1 weakGradient hPairing, ?_, ?_⟩
  · -- The constructed Sobolev element stores the original scalar in its `L¹` coordinate.
    exact W11.ofLp_toL1 toL1 weakGradient hPairing
  · -- The weak-gradient norm integral is unchanged by the `Lp` packaging and by the Riesz
    -- transport from Fréchet derivatives to Euclidean gradients.
    calc
      ∫ x, ‖(W11.ofLp toL1 weakGradient hPairing).weakGradient x‖ ∂domainMeasure Ω
          = ∫ x, ‖weakGradient x‖ ∂domainMeasure Ω := by
              rw [W11.ofLp_weakGradient]
      _ = ∫ x, ‖grad x‖ ∂domainMeasure Ω := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards [MeasureTheory.MemLp.coeFn_toLp hgradMem] with x hx
            simp [weakGradient, grad, hx]
      _ = ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω := by
            simpa [grad] using
              integral_norm_rieszGradient_eq_integral_norm_fderiv (Ω := Ω) (φ := φ)

/-- Helper for Theorem 8.16: the Chapter 8 total variation of a smooth scalar supported in `Ω`
matches the integral of its Fréchet derivative norm. -/
lemma smoothCompactSupport_totalVariationToReal_eq_integral_norm_fderiv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ_smooth : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subset : tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    (totalVariation
        (MeasureTheory.MemLp.toLp φ
          (hφ_smooth.continuous.memLp_of_hasCompactSupport
            (μ := domainMeasure Ω) hφ_compact))).toReal =
      ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω := by
  -- Package the smooth scalar into `W¹,¹(Ω)` and then rewrite total variation by Proposition 8.13.
  rcases
      smoothCompactSupport_memW11
        (Ω := Ω) (φ := φ) hφ_smooth hφ_compact hφ_subset with
    ⟨w, hw_toL1, hw_grad⟩
  calc
    (totalVariation
        (MeasureTheory.MemLp.toLp φ
          (hφ_smooth.continuous.memLp_of_hasCompactSupport
            (μ := domainMeasure Ω) hφ_compact))).toReal
        = (totalVariation w.toL1).toReal := by
            rw [hw_toL1]
    _ = ∫ x, ‖w.weakGradient x‖ ∂domainMeasure Ω := by
          exact totalVariation_toReal_eq_integral_norm_of_weakGradient w
    _ = ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω := hw_grad

/-- Helper for Theorem 8.16: any upper bound on the Chapter 8 total variation of a smooth scalar
supported in `Ω` immediately yields the corresponding derivative-integral bound. -/
lemma integral_norm_fderiv_le_of_smoothCompactSupport_totalVariationToReal_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    {B : ℝ}
    (hφ_smooth : ContDiff ℝ 1 φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_subset : tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hTV :
      (totalVariation
          (MeasureTheory.MemLp.toLp φ
            (hφ_smooth.continuous.memLp_of_hasCompactSupport
              (μ := domainMeasure Ω) hφ_compact))).toReal ≤ B) :
    ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤ B := by
  -- The previous identity moves the entire estimate from the BV surface to the derivative surface.
  rw [← smoothCompactSupport_totalVariationToReal_eq_integral_norm_fderiv
    (Ω := Ω) (φ := φ) hφ_smooth hφ_compact hφ_subset]
  exact hTV

/-- Helper for Theorem 8.16: a compact set inside `Ω` admits a smooth scalar cutoff whose support
is compactly contained in `Ω` and which is identically `1` on that compact core. -/
lemma existsSmoothCompactSupportCutoffOnCompactSubset
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    (hK_compact : IsCompact K)
    (hK_subset : K ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d)))) :
    ∃ η : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ η ∧
      HasCompactSupport η ∧
      tsupport η ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      Set.EqOn η 1 K ∧
      (∀ x, η x ∈ Set.Icc (0 : ℝ) 1) := by
  obtain ⟨L, hL_compact, hKL, hL_subset⟩ :=
    exists_compact_between hK_compact Ω.2 hK_subset
  obtain ⟨η, hη_cmdiff, hη_range, hη_support, hη_one⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d)))
      isOpen_interior hK_compact.isClosed hKL
  have hη_tsupport_subset : tsupport η ⊆ L := by
    rw [tsupport, hη_support]
    exact closure_minimal interior_subset hL_compact.isClosed
  have hη_tsupport_compact : IsCompact (tsupport η) :=
    hL_compact.of_isClosed_subset (isClosed_tsupport (f := η)) hη_tsupport_subset
  have hη_compact : HasCompactSupport η := by
    exact HasCompactSupport.intro hη_tsupport_compact fun x hx ↦
      image_eq_zero_of_notMem_tsupport hx
  refine ⟨η, hη_cmdiff.contDiff, hη_compact, hη_tsupport_subset.trans hL_subset, ?_, ?_⟩
  · intro x hx
    exact (hη_one x).1 hx
  · intro x
    exact hη_range ⟨x, rfl⟩

/-- Helper for Theorem 8.16: cutting an integrable scalar field by a smooth cutoff equal to `1`
on a compact core produces an `L¹` tail error controlled by the mass outside that core. -/
lemma cutoffTail_eLpNorm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {φ η : EuclideanSpace ℝ (Fin d) → ℝ}
    {K : Set (EuclideanSpace ℝ (Fin d))}
    {δ : ℝ}
    (hφInt : MeasureTheory.Integrable φ (domainMeasure Ω))
    (hK_compact : IsCompact K)
    (hη_cont : Continuous η)
    (hη_one : Set.EqOn η 1 K)
    (hη_range : ∀ x, η x ∈ Set.Icc (0 : ℝ) 1)
    (htail :
      ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), ‖φ x‖ ∂domainMeasure Ω ≤ δ) :
    MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal δ := by
  have hcutoffAesm :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ η x * φ x) (domainMeasure Ω) := by
    -- The cutoff localization is measurable because the cutoff is continuous and `φ` is `L¹`.
    exact hη_cont.aestronglyMeasurable.mul hφInt.aestronglyMeasurable
  have hcutoffInt :
      MeasureTheory.Integrable (fun x ↦ η x * φ x) (domainMeasure Ω) := by
    -- The range restriction `0 ≤ η ≤ 1` keeps the localized field dominated by `|φ|`.
    refine hφInt.norm.mono' hcutoffAesm ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hη0 : 0 ≤ η x := (hη_range x).1
      have hη1 : η x ≤ 1 := (hη_range x).2
      have hηnorm : ‖η x‖ ≤ 1 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hη0] using hη1
      calc
        ‖η x * φ x‖ = ‖η x‖ * ‖φ x‖ := norm_mul _ _
        _ ≤ ‖φ x‖ := by
          nlinarith [hηnorm, norm_nonneg (φ x)]
  have hcutoffErrorInt :
      MeasureTheory.Integrable (fun x ↦ φ x - η x * φ x) (domainMeasure Ω) := by
    -- The cutoff defect is integrable as a difference of two `L¹` scalars.
    exact hφInt.sub hcutoffInt
  have hcutoffError_le :
      ∫ x, ‖φ x - η x * φ x‖ ∂domainMeasure Ω ≤
        ∫ x in ((Ω : Set (EuclideanSpace ℝ (Fin d))) \ K), ‖φ x‖ ∂domainMeasure Ω := by
    let s : Set (EuclideanSpace ℝ (Fin d)) := (Ω : Set (EuclideanSpace ℝ (Fin d))) \ K
    have hs_meas : MeasurableSet s := Ω.2.measurableSet.diff hK_compact.isClosed.measurableSet
    have htailInt :
        MeasureTheory.Integrable (s.indicator fun x ↦ ‖φ x‖) (domainMeasure Ω) := by
      -- The tail indicator keeps the integrable norm density in `L¹`.
      exact hφInt.norm.indicator hs_meas
    have hpointwise :
        ∀ᵐ x ∂domainMeasure Ω, ‖φ x - η x * φ x‖ ≤ s.indicator (fun x ↦ ‖φ x‖) x := by
      -- On the compact core the cutoff is exactly `1`; on the tail, `0 ≤ η ≤ 1` bounds the
      -- localization defect by the ambient norm.
      rw [domainMeasure_def]
      refine
        (MeasureTheory.ae_restrict_iff'
          (μ := (MeasureTheory.Measure.euclideanHausdorffMeasure d :
            MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))))
          (s := (Ω : Set (EuclideanSpace ℝ (Fin d))))
          Ω.2.measurableSet).2 ?_
      refine Filter.Eventually.of_forall fun x hxΩ ↦ ?_
      by_cases hKx : x ∈ K
      · have hηx : η x = 1 := hη_one hKx
        have hsx : x ∉ s := by
          simp [s, hKx]
        simp [s, hsx, hηx]
      · have hη0 : 0 ≤ η x := (hη_range x).1
        have hη1 : η x ≤ 1 := (hη_range x).2
        have habs : |1 - η x| ≤ 1 := by
          have hnonneg : 0 ≤ 1 - η x := by linarith
          rw [abs_of_nonneg hnonneg]
          linarith
        have hcoeff : ‖1 - η x‖ ≤ 1 := by
          simpa [Real.norm_eq_abs] using habs
        have hnorm :
            ‖φ x - η x * φ x‖ ≤ ‖φ x‖ := by
          have hrewrite : φ x - η x * φ x = (1 - η x) * φ x := by ring
          calc
            ‖φ x - η x * φ x‖ = ‖(1 - η x) * φ x‖ := by rw [hrewrite]
            _ = ‖(1 - η x) • φ x‖ := by simp [smul_eq_mul]
            _ ≤ ‖1 - η x‖ * ‖φ x‖ := norm_smul_le _ _
            _ ≤ ‖φ x‖ := by
                nlinarith [hcoeff, norm_nonneg (φ x)]
        have hsx : x ∈ s := by
          simp [s, hxΩ, hKx]
        simpa [s, Set.indicator_of_mem hsx] using hnorm
    -- Integrate the pointwise tail domination on the restricted domain measure.
    refine
      (MeasureTheory.integral_mono_ae hcutoffErrorInt.norm htailInt hpointwise).trans ?_
    rw [MeasureTheory.integral_indicator hs_meas]
  -- For `p = 1`, convert the integral bound back to the `eLpNorm` normal form.
  calc
    MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω)
        = ENNReal.ofReal (∫ x, ‖φ x - η x * φ x‖ ∂domainMeasure Ω) := by
            rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
            symm
            exact MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hcutoffErrorInt
    _ ≤ ENNReal.ofReal δ := by
          exact ENNReal.ofReal_le_ofReal (hcutoffError_le.trans htail)

/-- Helper for Theorem 8.16: once both the ambient approximation error and the cutoff defect
consume half of the `L¹` budget, the triangle inequality closes the full error estimate. -/
lemma smoothApprox_triangle_eLpNorm_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {φ ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hφMem : MeasureTheory.MemLp φ 1 (domainMeasure Ω))
    (hψMem : MeasureTheory.MemLp ψ 1 (domainMeasure Ω))
    (hφ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2))
    (hψ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ φ x - ψ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2)) :
    MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - ψ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε := by
  have hε_half_nonneg : 0 ≤ ε / 2 := by
    linarith
  have huMem : MeasureTheory.MemLp u.toL1 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.memLp u.toL1
  have hleft :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ u.toL1 x - φ x) (domainMeasure Ω) :=
    (huMem.sub hφMem).aestronglyMeasurable
  have hright :
      MeasureTheory.AEStronglyMeasurable (fun x ↦ φ x - ψ x) (domainMeasure Ω) :=
    (hφMem.sub hψMem).aestronglyMeasurable
  have hsum :
      MeasureTheory.eLpNorm
          ((fun x ↦ u.toL1 x - φ x) + (fun x ↦ φ x - ψ x))
          1 (domainMeasure Ω) ≤
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) +
          MeasureTheory.eLpNorm (fun x ↦ φ x - ψ x) 1 (domainMeasure Ω) := by
    -- Keep the triangle inequality on the two explicit `L¹` defects, avoiding extra transport.
    exact MeasureTheory.eLpNorm_add_le hleft hright (by simp : (1 : ENNReal) ≤ 1)
  have hrewrite :
      (fun x ↦ u.toL1 x - ψ x) =
        (fun x ↦ u.toL1 x - φ x) + (fun x ↦ φ x - ψ x) := by
    ext x
    simp [Pi.add_apply]
  calc
    MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - ψ x) 1 (domainMeasure Ω)
        = MeasureTheory.eLpNorm
            ((fun x ↦ u.toL1 x - φ x) + (fun x ↦ φ x - ψ x))
            1 (domainMeasure Ω) := by
              rw [hrewrite]
    _ ≤ MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) +
          MeasureTheory.eLpNorm (fun x ↦ φ x - ψ x) 1 (domainMeasure Ω) := hsum
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          add_le_add hφ_eLp hψ_eLp
    _ = ENNReal.ofReal ε := by
          rw [← ENNReal.ofReal_add hε_half_nonneg hε_half_nonneg]
          ring

/-- Helper for Theorem 8.16: multiplying an ambient smooth approximant by a compactly supported
cutoff restores support inside `Ω` while preserving the final `L¹` error budget. -/
lemma cutoffRestoreSmoothL1Approx
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {φ η : EuclideanSpace ℝ (Fin d) → ℝ}
    {ε : ℝ}
    (hε : 0 ≤ ε)
    (hφ_smooth : ContDiff ℝ ∞ φ)
    (hφ_compact : HasCompactSupport φ)
    (hη_smooth : ContDiff ℝ ∞ η)
    (hη_compact : HasCompactSupport η)
    (hη_subset : tsupport η ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))))
    (hφ_eLp :
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2))
    (hcutoffError_eLp :
      MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2)) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ ψ ∧
      HasCompactSupport ψ ∧
      tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - ψ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε := by
  let ψ : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ η x * φ x
  have hφMem : MeasureTheory.MemLp φ 1 (domainMeasure Ω) := by
    -- Smooth compact support places the ambient approximant in `L¹(domainMeasure Ω)`.
    exact hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    -- Multiplying by the smooth cutoff preserves smoothness of the ambient approximant.
    simpa [ψ] using hη_smooth.mul hφ_smooth
  have hψ_compact : HasCompactSupport ψ := by
    -- The restored approximant inherits compact support from the cutoff.
    change HasCompactSupport (η * φ)
    simpa [ψ] using hη_compact.mul_right (f' := φ)
  have hψ_subset : tsupport ψ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) := by
    -- The topological support of the restored approximant stays inside the cutoff support.
    simpa [ψ] using (tsupport_mul_subset_left (f := η) (g := φ)).trans hη_subset
  have hψMem : MeasureTheory.MemLp ψ 1 (domainMeasure Ω) := by
    -- Smooth compact support keeps the restored approximant in `L¹(domainMeasure Ω)`.
    exact hψ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hψ_compact
  refine ⟨ψ, hψ_smooth, hψ_compact, hψ_subset, ?_⟩
  -- The pure `L¹` estimate is now isolated in a small triangle-inequality helper.
  exact
    smoothApprox_triangle_eLpNorm_le
      (Ω := Ω) (u := u) (φ := φ) (ψ := ψ) (ε := ε) hε
      hφMem hψMem hφ_eLp (by simpa [ψ] using hcutoffError_eLp)

/-- Helper for Theorem 8.16: every `BV(Ω)` element admits a smooth scalar approximation with
compact support inside `Ω` and arbitrarily small `L¹` error on `domainMeasure Ω`. -/
theorem existsSmoothCompactSupportL1Approx_of_bv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε := by
  have hε_half : 0 < ε / 2 := by linarith
  -- Route correction: separate the ambient approximation, tail cutoff estimate, and final
  -- support-restoration step so the theorem stays a short assembly owner.
  have huMem : MeasureTheory.MemLp u.toL1 1 (domainMeasure Ω) := by
    exact MeasureTheory.Lp.memLp u.toL1
  obtain ⟨φ, hφ_compact, hφ_smooth, hφ_eLp⟩ :=
    MeasureTheory.MemLp.exist_eLpNorm_sub_le
      (μ := domainMeasure Ω) (p := (1 : ENNReal)) (by simp) (by simp) huMem
      (ε := ε / 2) hε_half
  have hφMem : MeasureTheory.MemLp φ 1 (domainMeasure Ω) := by
    exact hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact
  have hφInt : MeasureTheory.Integrable φ (domainMeasure Ω) := by
    simpa [MeasureTheory.memLp_one_iff_integrable] using hφMem
  obtain ⟨K, hK_subset, hK_compact, hK_tail⟩ :=
    existsCompactSubset_tailIntegral_lt
      (Ω := Ω) (h := fun x ↦ ‖φ x‖) hφInt.norm (fun _ ↦ norm_nonneg _) hε_half
  obtain ⟨η, hη_smooth, hη_compact, hη_subset, hη_one, hη_range⟩ :=
    existsSmoothCompactSupportCutoffOnCompactSubset
      (Ω := Ω) hK_compact hK_subset
  have hcutoffError_eLp :
      MeasureTheory.eLpNorm (fun x ↦ φ x - η x * φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal (ε / 2) := by
    -- The cutoff estimate is now its own theorem-local bridge.
    exact
      cutoffTail_eLpNorm_le
        (Ω := Ω) (φ := φ) (η := η) (K := K) (δ := ε / 2)
        hφInt hK_compact hη_smooth.continuous hη_one hη_range
        (le_of_lt <| by simpa using hK_tail)
  -- Finish by packaging the localized approximant through the dedicated support-restoration
  -- helper, rather than replaying the whole triangle argument inline.
  exact
    cutoffRestoreSmoothL1Approx
      (Ω := Ω) (u := u) (φ := φ) (η := η) (ε := ε) (le_of_lt hε)
      hφ_smooth hφ_compact hη_smooth hη_compact hη_subset hφ_eLp hcutoffError_eLp

/-- Helper for Theorem 8.16: strict `BV` approximation by smooth compactly supported scalars with
independently chosen `L¹` and derivative budgets. -/
theorem existsSmoothCompactSupportApprox_of_bv_twoBudgetsDeriv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {δ η : ℝ}
    (hδ : 0 < δ)
    (hη : 0 < η) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤
        ENNReal.ofReal δ ∧
      ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤
        (totalVariation u.toL1).toReal + η := by
  -- Route correction: select a single one-shot strict-BV approximant at the minimum budget,
  -- instead of maintaining a second local recovery-sequence owner in this bridge file.
  have hmin_pos : 0 < min δ η := lt_min hδ hη
  rcases
      existsSmoothCompactSupportApprox_of_bv
        (d := d) (Ω := Ω) (u := u) (ε := min δ η) hmin_pos with
    ⟨φ, hφ_smooth, hφ_compact, hφ_subset, hφ_err, hφ_deriv⟩
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_subset, ?_, ?_⟩
  · -- The reciprocal-budget witness already satisfies the requested `L¹` tolerance.
    exact hφ_err.trans <| ENNReal.ofReal_le_ofReal (min_le_left _ _)
  · -- The derivative estimate is reduced to the same Archimedean budget choice.
    have hη_le : min δ η ≤ η := min_le_right _ _
    linarith

/-- Helper for Theorem 8.16: strict `BV` approximation by smooth compactly supported scalars with
controlled Chapter 8 total variation. -/
theorem existsSmoothCompactSupportApprox_of_bv_totalVariationToReal_le
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ∃ hφ_mem : MeasureTheory.MemLp φ 1 (domainMeasure Ω),
        ContDiff ℝ ∞ φ ∧
        HasCompactSupport φ ∧
        tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
        MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε ∧
        (totalVariation (MeasureTheory.MemLp.toLp φ hφ_mem)).toReal ≤
          (totalVariation u.toL1).toReal + ε := by
  -- Route correction: specialize the derivative-surface recovery theorem, then transport that
  -- derivative estimate back to total variation by the smooth identity proved above.
  rcases
      existsSmoothCompactSupportApprox_of_bv_twoBudgetsDeriv
        (d := d) (Ω := Ω) (u := u) (δ := ε) (η := ε) hε hε with
    ⟨φ, hφ_smooth, hφ_compact, hφ_subset, hφ_err, hφ_deriv⟩
  have hφ_mem : MeasureTheory.MemLp φ 1 (domainMeasure Ω) := by
    -- Continuity plus compact support is the canonical `L¹` witness for a smooth scalar.
    exact hφ_smooth.continuous.memLp_of_hasCompactSupport (μ := domainMeasure Ω) hφ_compact
  refine ⟨φ, hφ_mem, hφ_smooth, hφ_compact, hφ_subset, hφ_err, ?_⟩
  have horder : (1 : ℕ∞) ≤ ∞ := by
    simp
  have hφ_smooth_one : ContDiff ℝ 1 φ := by
    exact hφ_smooth.of_le horder
  have hφ_tv_eq :
      (totalVariation (MeasureTheory.MemLp.toLp φ hφ_mem)).toReal =
        ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω := by
    -- The `L¹` packaging proof is irrelevant, so the previously proved smooth identity applies.
    simpa using
      (smoothCompactSupport_totalVariationToReal_eq_integral_norm_fderiv
        (Ω := Ω) (φ := φ) hφ_smooth_one hφ_compact hφ_subset)
  rw [hφ_tv_eq]
  exact hφ_deriv

/-- Helper for Theorem 8.16: every `BV(Ω)` element should admit a smooth compactly supported
approximation supported in `Ω`, with arbitrarily small `L¹` error and derivative integral
controlled by its total variation. -/
theorem existsSmoothCompactSupportApprox_of_bv
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    [MeasureTheory.IsFiniteMeasure (domainMeasure Ω)]
    (u : BV Ω)
    {ε : ℝ}
    (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ φ ∧
      HasCompactSupport φ ∧
      tsupport φ ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      MeasureTheory.eLpNorm (fun x ↦ u.toL1 x - φ x) 1 (domainMeasure Ω) ≤ ENNReal.ofReal ε ∧
      ∫ x, ‖fderiv ℝ φ x‖ ∂domainMeasure Ω ≤ (totalVariation u.toL1).toReal + ε := by
  -- Route correction: reduce the derivative estimate to one theorem-local strict BV approximation
  -- owner, then move the total-variation bound across Proposition 8.13's derivative identity.
  rcases
      existsSmoothCompactSupportApprox_of_bv_totalVariationToReal_le
        (d := d) (Ω := Ω) u hε with
    ⟨φ, hφ_mem, hφ_smooth, hφ_compact, hφ_subset, hφ_err, hφ_tv⟩
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_subset, hφ_err, ?_⟩
  -- The auxiliary total-variation control is exactly the hypothesis consumed by the derivative
  -- bridge proved earlier in this file.
  have hφ_tv' :
      (totalVariation
          (MeasureTheory.MemLp.toLp φ
            (hφ_smooth.continuous.memLp_of_hasCompactSupport
              (μ := domainMeasure Ω) hφ_compact))).toReal ≤
        (totalVariation u.toL1).toReal + ε := by
    simpa using hφ_tv
  have horder : (1 : ℕ∞) ≤ ∞ := by
    simp
  have hcontDiff_one : ContDiff ℝ 1 φ := by
    exact hφ_smooth.of_le horder
  exact
    integral_norm_fderiv_le_of_smoothCompactSupport_totalVariationToReal_le
      (Ω := Ω) (φ := φ) (B := (totalVariation u.toL1).toReal + ε)
      hcontDiff_one hφ_compact hφ_subset hφ_tv'

end BVCompactness

end VariationalRegularization

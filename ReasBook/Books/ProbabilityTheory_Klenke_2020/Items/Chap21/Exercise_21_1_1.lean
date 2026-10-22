/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.HolderNorm
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Bases
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Topology.MetricSpace.Lipschitz

public section

open MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E] [CompleteSpace E] [SecondCountableTopology E]
variable {d : ℕ}

/-- A process has locally Hölder sample paths of exponent `γ` if every sample path is locally
Hölder of order `γ` on the Euclidean parameter space. -/
def HasLocallyHolderPaths (γ : ℝ≥0) (Y : EuclideanSpace ℝ (Fin d) → Ω → E) : Prop :=
  ∀ ω : Ω, ∀ x : EuclideanSpace ℝ (Fin d),
    ∃ s : Set (EuclideanSpace ℝ (Fin d)), s ∈ 𝓝 x ∧
      ∃ C : ℝ≥0, HolderOnWith C γ (fun t ↦ Y t ω) s

/-- Helper for Exercise 21.1.1: the closed cube `[-T, T]^d` in `ℝ^d`, viewed as a subset of
`EuclideanSpace ℝ (Fin d)`. -/
def euclideanClosedCube (d : ℕ) (T : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc (-T) T}

/-- Helper for Exercise 21.1.1: a map is locally Hölder of exponent `r` if every point has a
neighborhood on which it is `HolderWith r`. This is kept theorem-local to avoid depending on the
non-`module` statement-stage file `Definition_21_2`. -/
private def LocallyHolderWith
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (r : ℝ≥0) (f : X → Y) : Prop :=
  ∀ x : X, ∃ s : Set X, s ∈ 𝓝 x ∧ ∃ C : ℝ≥0, HolderOnWith C r f s

/-- Helper for Exercise 21.1.1: in a metric space, a local Hölder witness can be shrunk to a
metric ball. -/
private theorem LocallyHolderWith.exists_holderOnWith_ball
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {r : ℝ≥0} {f : X → Y}
    (hf : LocallyHolderWith r f) (x : X) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ≥0, HolderOnWith C r f (Metric.ball x ε) := by
  rcases hf x with ⟨s, hs, C, hC⟩
  -- Proof comment: convert the neighborhood witness into a concrete ball and restrict the
  -- Hölder estimate to that smaller set.
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, hεpos, hεsubset⟩
  exact ⟨ε, hεpos, C, hC.mono hεsubset⟩

/-- Helper for Exercise 21.1.1: membership in `euclideanClosedCube d T` is exactly the
coordinatewise condition `x i ∈ [-T, T]`. -/
theorem mem_euclideanClosedCube_iff {T : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ euclideanClosedCube d T ↔ ∀ i : Fin d, x i ∈ Set.Icc (-T) T :=
  Iff.rfl

/-- Helper for Exercise 21.1.1: the source-facing multidimensional Kolmogorov condition on the
closed cube `[-T, T]^d`, packaged through the canonical owner
`ProbabilityTheory.IsKolmogorovProcess`. -/
def IsKolmogorovProcessOnEuclideanClosedCube
    (μ : Measure Ω) (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T α β C : ℝ≥0) : Prop :=
  IsKolmogorovProcess (fun t : euclideanClosedCube d (T : ℝ) ↦ X t) μ (α : ℝ)
    (((d : ℝ≥0) + β : ℝ)) C

/-- Helper for Exercise 21.1.1: a cube-owner Kolmogorov hypothesis gives the corresponding
increment estimate on cube points. -/
theorem IsKolmogorovProcessOnEuclideanClosedCube.increment_lintegral_le
    {μ : Measure Ω} {X : EuclideanSpace ℝ (Fin d) → Ω → E}
    {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    {s t : EuclideanSpace ℝ (Fin d)}
    (hs : s ∈ euclideanClosedCube d (T : ℝ))
    (ht : t ∈ euclideanClosedCube d (T : ℝ)) :
    ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
      (C : ℝ≥0∞) * edist t s ^ (((d : ℝ≥0) + β : ℝ)) := by
  -- Proof comment: the owner hypothesis already lives on the cube subtype, so the ambient-point
  -- statement is just the subtype estimate with coercions simplified away.
  simpa [edist_comm] using h.kolmogorovCondition ⟨s, hs⟩ ⟨t, ht⟩

/-- Helper for Exercise 21.1.1: an `edist^α` moment bound yields the corresponding real-valued
tail estimate for strict distance superlevel sets. -/
theorem measureReal_edist_gt_le_of_lintegral_bound
    {μ : Measure Ω} {Y Z : Ω → E} {α δ M : ℝ}
    (hα : 0 < α)
    (hδ : 0 < δ)
    (hM : 0 ≤ M)
    (hmeas : AEMeasurable (fun ω ↦ edist (Y ω) (Z ω) ^ α) μ)
    (hlintegral : ∫⁻ ω, edist (Y ω) (Z ω) ^ α ∂μ ≤ ENNReal.ofReal M) :
    μ.real {ω | δ < dist (Y ω) (Z ω)} ≤ M / δ ^ α := by
  have hδpow_pos : 0 < δ ^ α := Real.rpow_pos_of_pos hδ α
  have hδpow_ne0 : ENNReal.ofReal (δ ^ α) ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr hδpow_pos).ne'
  have hstrict_subset :
      {ω | δ < dist (Y ω) (Z ω)} ⊆
        {ω | ENNReal.ofReal (δ ^ α) ≤ edist (Y ω) (Z ω) ^ α} := by
    intro ω hω
    -- Proof comment: positivity of `α` lets us raise the strict real threshold to the
    -- corresponding ENNReal threshold used in Markov's inequality.
    have hωpow : δ ^ α ≤ dist (Y ω) (Z ω) ^ α :=
      Real.rpow_le_rpow hδ.le hω.le hα.le
    simpa [Set.mem_setOf_eq, edist_dist, ENNReal.ofReal_rpow_of_nonneg hδ.le hα.le,
      ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist (Y ω) (Z ω)) hα.le] using
      ENNReal.ofReal_le_ofReal hωpow
  have hmarkov :
      μ {ω | ENNReal.ofReal (δ ^ α) ≤ edist (Y ω) (Z ω) ^ α} ≤
        (∫⁻ ω, edist (Y ω) (Z ω) ^ α ∂μ) / ENNReal.ofReal (δ ^ α) :=
    MeasureTheory.meas_ge_le_lintegral_div hmeas hδpow_ne0 ENNReal.ofReal_ne_top
  have hμ :
      μ {ω | δ < dist (Y ω) (Z ω)} ≤ ENNReal.ofReal (M / δ ^ α) := by
    calc
      μ {ω | δ < dist (Y ω) (Z ω)} ≤
          μ {ω | ENNReal.ofReal (δ ^ α) ≤ edist (Y ω) (Z ω) ^ α} :=
        measure_mono hstrict_subset
      _ ≤ (∫⁻ ω, edist (Y ω) (Z ω) ^ α ∂μ) / ENNReal.ofReal (δ ^ α) := hmarkov
      _ ≤ ENNReal.ofReal M / ENNReal.ofReal (δ ^ α) := by
        simpa using ENNReal.div_le_div_right hlintegral (ENNReal.ofReal (δ ^ α))
      _ = ENNReal.ofReal (M / δ ^ α) := by
            rw [ENNReal.ofReal_div_of_pos hδpow_pos]
  -- Proof comment: once the ENNReal Markov estimate is normalized, convert it to the
  -- real-valued `measureReal` form needed for Borel-Cantelli estimates.
  have hdiv_nonneg : 0 ≤ M / δ ^ α := by
    positivity
  exact ENNReal.toReal_le_of_le_ofReal hdiv_nonneg hμ

/-- Helper for Exercise 21.1.1: the nested cube radius used in the patching argument is
`n + 1`. -/
private def closedCubeRadius (n : ℕ) : ℝ≥0 :=
  n + 1

/-- Helper for Exercise 21.1.1: every nested closed-cube radius is positive. -/
private lemma closedCubeRadius_pos (n : ℕ) : 0 < closedCubeRadius n := by
  simp [closedCubeRadius]

/-- Helper for Exercise 21.1.1: the `n`-th nested closed cube is `[-(n+1), n+1]^d`. -/
private abbrev nestedClosedCube (d : ℕ) (n : ℕ) :=
  euclideanClosedCube d ((closedCubeRadius n : ℝ))

/-- Helper for Exercise 21.1.1: every coordinate of a Euclidean vector is bounded by its norm. -/
private lemma abs_apply_le_norm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x i| ≤ ‖x‖ := by
  have hsum :
      (x i) ^ 2 ≤ ∑ j : Fin d, (x j) ^ 2 := by
    simpa using Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (by simp)
  have hsq : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa [EuclideanSpace.real_norm_sq_eq] using hsum
  have habs_sq : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    simpa [sq_abs] using hsq
  nlinarith [abs_nonneg (x i), norm_nonneg x, habs_sq]

/-- Helper for Exercise 21.1.1: the origin belongs to every nonnegative closed cube. -/
private lemma zero_mem_euclideanClosedCube {T : ℝ} (hT : 0 ≤ T) :
    (0 : EuclideanSpace ℝ (Fin d)) ∈ euclideanClosedCube d T := by
  intro i
  simp [hT]

/-- Helper for Exercise 21.1.1: the nested cube radii are monotone. -/
private lemma closedCubeRadius_mono {m n : ℕ} (hmn : m ≤ n) :
    ((closedCubeRadius m : ℝ≥0) : ℝ) ≤ (closedCubeRadius n : ℝ) := by
  norm_num [closedCubeRadius]
  exact_mod_cast hmn

/-- Helper for Exercise 21.1.1: a smaller Euclidean closed cube sits inside every larger one. -/
private lemma euclideanClosedCube_mono {S T : ℝ} (hST : S ≤ T) :
    euclideanClosedCube d S ⊆ euclideanClosedCube d T := by
  intro x hx i
  rcases hx i with ⟨hxL, hxR⟩
  constructor
  · linarith
  · exact le_trans hxR hST

/-- Helper for Exercise 21.1.1: inclusion of nested closed cubes is given by the identity on the
ambient Euclidean space. -/
private def closedCubeInclusion {m n : ℕ} (hmn : m ≤ n) :
    nestedClosedCube d m → nestedClosedCube d n :=
  fun x ↦ ⟨x.1, euclideanClosedCube_mono (d := d) (closedCubeRadius_mono hmn) x.2⟩

/-- Helper for Exercise 21.1.1: nested closed-cube inclusions compose as expected. -/
private lemma closedCubeInclusion_comp {m n k : ℕ} (hmn : m ≤ n) (hnk : n ≤ k)
    (x : nestedClosedCube d m) :
    closedCubeInclusion (d := d) hnk (closedCubeInclusion (d := d) hmn x) =
      closedCubeInclusion (d := d) (le_trans hmn hnk) x := by
  rfl

/-- Helper for Exercise 21.1.1: every point lies in the nested cube indexed by the ceiling of its
norm. -/
private lemma self_mem_nestedClosedCube (x : EuclideanSpace ℝ (Fin d)) :
    x ∈ nestedClosedCube d (Nat.ceil ‖x‖) := by
  intro i
  have hcoord : |x i| ≤ ‖x‖ := abs_apply_le_norm (d := d) x i
  have hradius : ‖x‖ ≤ (closedCubeRadius (Nat.ceil ‖x‖) : ℝ) := by
    have hceil : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil ‖x‖
    norm_num [closedCubeRadius]
    linarith
  simpa [Set.mem_Icc] using abs_le.mp (le_trans hcoord hradius)

/-- Helper for Exercise 21.1.1: the closed cube of radius `n + 1` is nonempty. -/
private lemma nonempty_nestedClosedCube (n : ℕ) :
    Nonempty (nestedClosedCube d n) :=
  ⟨⟨0, zero_mem_euclideanClosedCube (d := d) <| by
      positivity⟩⟩

/-- Helper for Exercise 21.1.1: fix a dense sequence on each nested closed cube. -/
private noncomputable def closedCubeDensePoint (n : ℕ) :
    ℕ → nestedClosedCube d n :=
  let _ : Nonempty (nestedClosedCube d n) := nonempty_nestedClosedCube (d := d) n
  TopologicalSpace.denseSeq (nestedClosedCube d n)

/-- Helper for Exercise 21.1.1: the chosen dense sequence is indeed dense in the corresponding
nested closed cube. -/
private lemma denseRange_closedCubeDensePoint (n : ℕ) :
    DenseRange (closedCubeDensePoint (d := d) n) := by
  let _ : Nonempty (nestedClosedCube d n) := nonempty_nestedClosedCube (d := d) n
  simpa [closedCubeDensePoint] using
    (TopologicalSpace.denseRange_denseSeq (nestedClosedCube d n))

/-- Helper for Exercise 21.1.1: a point in the unit ball around `x` lies in the next larger
nested closed cube centered at the origin. -/
private lemma mem_nestedClosedCube_of_mem_ball {x t : EuclideanSpace ℝ (Fin d)}
    (ht : t ∈ Metric.ball x 1) :
    t ∈ nestedClosedCube d (Nat.ceil ‖x‖ + 1) := by
  have hdist : dist t x < 1 := Metric.mem_ball.1 ht
  have hnorm : ‖t‖ ≤ ‖x‖ + 1 := by
    have hlt :
        ‖t‖ < ‖x‖ + 1 := by
      calc
        ‖t‖ = ‖(t - x) + x‖ := by abel_nf
        _ ≤ ‖t - x‖ + ‖x‖ := norm_add_le _ _
        _ < 1 + ‖x‖ := by
              gcongr
              simpa [dist_eq_norm] using hdist
        _ = ‖x‖ + 1 := by ring
    exact le_of_lt hlt
  intro i
  have hcoord : |t i| ≤ ‖t‖ := abs_apply_le_norm (d := d) t i
  have hradius : ‖x‖ + 1 ≤ (closedCubeRadius (Nat.ceil ‖x‖ + 1) : ℝ) := by
    have hceil : ‖x‖ ≤ (Nat.ceil ‖x‖ : ℝ) := Nat.le_ceil ‖x‖
    norm_num [closedCubeRadius]
    linarith
  simpa [Set.mem_Icc] using abs_le.mp (le_trans hcoord <| le_trans hnorm hradius)

/-- Helper for Exercise 21.1.1: on a nested cube, agreement on the chosen dense sequence upgrades
to agreement everywhere once both paths are Hölder. -/
private lemma eqOn_nestedClosedCube_of_denseEq
    {n : ℕ}
    {f : nestedClosedCube d n → E}
    {g : nestedClosedCube d (n + 1) → E}
    {Kf Kg : ℝ≥0}
    (hγ₀ : 0 < γ)
    (hf : HolderWith Kf γ f)
    (hg : HolderWith Kg γ g)
    (hDenseEq :
      ∀ k : ℕ,
        f (closedCubeDensePoint (d := d) n k) =
          g (closedCubeInclusion (d := d) (Nat.le_succ n)
            (closedCubeDensePoint (d := d) n k))) :
    ∀ t : nestedClosedCube d n,
      f t = g (closedCubeInclusion (d := d) (Nat.le_succ n) t) := by
  let gSmall : nestedClosedCube d n → E :=
    fun t ↦ g (closedCubeInclusion (d := d) (Nat.le_succ n) t)
  have hgSmall : HolderWith Kg γ gSmall := by
    -- Proof comment: the nested-cube inclusion is the identity on the ambient Euclidean space, so
    -- the Hölder estimate restricts verbatim to the smaller cube.
    intro s t
    simpa [gSmall, closedCubeInclusion] using
      hg (closedCubeInclusion (d := d) (Nat.le_succ n) s)
        (closedCubeInclusion (d := d) (Nat.le_succ n) t)
  let seq : ℕ → nestedClosedCube d n := closedCubeDensePoint (d := d) n
  have hseqDense : Dense (Set.range seq) := by
    simpa [DenseRange, seq] using denseRange_closedCubeDensePoint (d := d) n
  have hEqOn : Set.EqOn f gSmall (Set.range seq) := by
    intro t ht
    rcases ht with ⟨k, rfl⟩
    simpa [seq, gSmall] using hDenseEq k
  -- Proof comment: Hölder paths are continuous, so equality on a dense set forces equality on
  -- the whole compact cube.
  have hfun : f = gSmall :=
    Continuous.ext_on hseqDense (hf.continuous hγ₀) (hgSmall.continuous hγ₀) hEqOn
  intro t
  exact congrFun hfun t

/-- Helper for Exercise 21.1.1: on the full-measure good branch where adjacent nested-cube
versions agree on dense sequences, all nested-cube versions are compatible on overlaps. -/
private lemma nestedCubeVersion_eq_of_good
    (Y : ∀ n : ℕ, nestedClosedCube d n → Ω → E)
    (hHolder :
      ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderWith K γ (fun t : nestedClosedCube d n ↦ Y n t ω))
    (hγ₀ : 0 < γ)
    {ω : Ω}
    (hGood :
      ∀ n k,
        Y n (closedCubeDensePoint (d := d) n k) ω =
          Y (n + 1)
            (closedCubeInclusion (d := d) (Nat.le_succ n)
              (closedCubeDensePoint (d := d) n k)) ω) :
    ∀ {m n : ℕ} (hmn : m ≤ n) (t : nestedClosedCube d m),
      Y m t ω = Y n (closedCubeInclusion (d := d) hmn t) ω := by
  intro m n hmn
  induction hmn with
  | refl =>
      intro t
      rfl
  | @step n hmn ih =>
      intro t
      rcases hHolder n ω with ⟨Kn, hKn⟩
      rcases hHolder (n + 1) ω with ⟨Kn1, hKn1⟩
      have hadj :
          ∀ s : nestedClosedCube d n,
            Y n s ω =
              Y (n + 1) (closedCubeInclusion (d := d) (Nat.le_succ n) s) ω :=
        eqOn_nestedClosedCube_of_denseEq
          (d := d)
          (γ := γ)
          (hγ₀ := hγ₀)
          (f := fun s ↦ Y n s ω)
          (g := fun s ↦ Y (n + 1) s ω)
          hKn
          hKn1
          (hDenseEq := hGood n)
      calc
        Y m t ω = Y n (closedCubeInclusion (d := d) hmn t) ω := ih t
        _ = Y (n + 1)
              (closedCubeInclusion (d := d) (Nat.le_succ n)
                (closedCubeInclusion (d := d) hmn t)) ω := hadj _
        _ = Y (n + 1)
              (closedCubeInclusion (d := d) (le_trans hmn (Nat.le_succ n)) t) ω := by
              rw [closedCubeInclusion_comp]

/-- Helper for Exercise 21.1.1: on the zero-radius cube, every point is the origin. -/
private lemma eq_zero_of_mem_euclideanClosedCube_zero
    (t : euclideanClosedCube d (0 : ℝ)) :
    (t : EuclideanSpace ℝ (Fin d)) = 0 := by
  -- Proof comment: each coordinate lies in the degenerate interval `[0, 0]`, so every
  -- coordinate vanishes.
  ext i
  have hi : t.1 i ∈ Set.Icc (0 : ℝ) 0 := by
    simpa [euclideanClosedCube] using t.2 i
  exact le_antisymm (Set.mem_Icc.mp hi).2 (Set.mem_Icc.mp hi).1

/-- Helper for Exercise 21.1.1: the closed cube `euclideanClosedCube d T` is compact. -/
private lemma isCompact_euclideanClosedCube (T : ℝ) :
    IsCompact (euclideanClosedCube d T) := by
  -- Proof comment: in finite-dimensional Euclidean space, closed and bounded sets are compact.
  have hClosed : IsClosed (euclideanClosedCube d T) := by
    have hEq :
        euclideanClosedCube d T =
          ⋂ i : Fin d, {x : EuclideanSpace ℝ (Fin d) | x i ∈ Set.Icc (-T) T} := by
      ext x
      simp [euclideanClosedCube]
    rw [hEq]
    refine isClosed_iInter fun i ↦ ?_
    have hcont : Continuous fun x : EuclideanSpace ℝ (Fin d) ↦ x.ofLp i :=
      (continuous_apply i).comp (PiLp.continuous_ofLp 2 (fun _ : Fin d ↦ ℝ))
    exact
      (isClosed_Icc : IsClosed (Set.Icc (-T) T : Set ℝ)).preimage
        hcont
  have hBounded :
      Bornology.IsBounded (euclideanClosedCube d T) := by
    have hsubset :
        euclideanClosedCube d T ⊆
          Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) (((d : ℝ) + 1) * |T|) := by
      intro x hx
      have hcoord : ∀ i : Fin d, |x i| ≤ |T| := by
        intro i
        rcases hx i with ⟨hL, hR⟩
        have hTnonneg : 0 ≤ T := by
          linarith
        have hL' : -|T| ≤ x i := by
          simpa [abs_of_nonneg hTnonneg] using hL
        have hR' : x i ≤ |T| := by
          simpa [abs_of_nonneg hTnonneg] using hR
        exact abs_le.2 ⟨hL', hR'⟩
      have hsq :
          ‖x‖ ^ 2 ≤ (d : ℝ) * |T| ^ 2 := by
        calc
          ‖x‖ ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
            simpa [EuclideanSpace.real_norm_sq_eq]
          _ ≤ ∑ i : Fin d, |T| ^ 2 := by
                refine Finset.sum_le_sum fun i _ ↦ ?_
                have hsq_i : (x i) ^ 2 ≤ |T| ^ 2 := by
                  have habs_sq : |x i| ^ 2 ≤ |T| ^ 2 := by
                    nlinarith [abs_nonneg (x i), abs_nonneg T, hcoord i]
                  simpa [sq_abs] using habs_sq
                exact hsq_i
          _ = (d : ℝ) * |T| ^ 2 := by
                simp
      have hsq_bound :
          (d : ℝ) * |T| ^ 2 ≤ ((((d : ℝ) + 1) * |T|) : ℝ) ^ 2 := by
        nlinarith [abs_nonneg T]
      have hnorm : ‖x‖ ≤ (((d : ℝ) + 1) * |T| : ℝ) := by
        refine le_of_sq_le_sq ?_ (by positivity)
        exact le_trans hsq hsq_bound
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
    exact
      (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin d)) (((d : ℝ) + 1) * |T|)).isBounded.subset
        hsubset
  exact Metric.isCompact_of_isClosed_isBounded hClosed hBounded

/-- Helper for Exercise 21.1.1: a locally Hölder map of positive exponent between metric spaces is
continuous. -/
private lemma continuous_of_locallyHolderWithMetric
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {q : ℝ≥0} {f : X → Y}
    (hq : 0 < q)
    (hf : LocallyHolderWith q f) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  rcases hf x with ⟨s, hs, C, hC⟩
  -- Proof comment: a local Hölder witness is continuous on its neighborhood, so continuity at the
  -- center follows immediately.
  have hx : x ∈ s := mem_of_mem_nhds hs
  exact (hC.continuousOn hq x hx).continuousAt hs

/-- Helper for Exercise 21.1.1: on a compact metric space, local Hölder control can be made
uniform on sufficiently small distances. -/
private lemma exists_uniformLocalHolderBound_of_compactMetric
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y] [CompactSpace X] [Nonempty X]
    {q : ℝ≥0} {f : X → Y}
    (hf : LocallyHolderWith q f) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ x y, dist x y < δ →
      dist (f x) (f y) ≤ C * dist x y ^ (q : ℝ) := by
  classical
  choose ε hε C hC using fun x => hf.exists_holderOnWith_ball x
  let U : X → Set X := fun x ↦ Metric.ball x (ε x / 2)
  have hcover : (Set.univ : Set X) ⊆ ⋃ x, U x := by
    intro x _
    refine Set.mem_iUnion.2 ⟨x, ?_⟩
    exact Metric.mem_ball_self (half_pos (hε x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U (fun _ => Metric.isOpen_ball) hcover
  have hcover' : (Set.univ : Set X) ⊆ ⋃ i : {x // x ∈ t}, U i.1 := by
    intro x hx
    rcases Set.mem_iUnion.1 (ht hx) with ⟨i, hxi⟩
    rcases Set.mem_iUnion.1 hxi with ⟨hi, hxU⟩
    exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, hxU⟩
  obtain ⟨δ, hδpos, hδ⟩ := lebesgue_number_lemma_of_metric isCompact_univ
    (fun _ => Metric.isOpen_ball) hcover'
  let C₀ : ℝ≥0 := t.sup C
  refine ⟨δ, hδpos, C₀, ?_⟩
  intro x y hxy
  -- Proof comment: the Lebesgue radius places both points in a single local witness ball, and the
  -- finite supremum of the witness constants gives a uniform estimate.
  have hxδ : x ∈ Metric.ball x δ := Metric.mem_ball_self hδpos
  rcases hδ x (by simp) with ⟨i, hi⟩
  have hxU : x ∈ U i.1 := hi hxδ
  have hyU : y ∈ U i.1 := hi <| by
    simpa [dist_comm] using Metric.mem_ball.2 hxy
  have hhalf_le : ε i.1 / 2 ≤ ε i.1 := by
    nlinarith [hε i.1]
  have hxBall : x ∈ Metric.ball i.1 (ε i.1) := by
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hxU).trans_le hhalf_le
  have hyBall : y ∈ Metric.ball i.1 (ε i.1) := by
    exact Metric.mem_ball.2 <| (Metric.mem_ball.1 hyU).trans_le hhalf_le
  have hlocal : dist (f x) (f y) ≤ C i.1 * dist x y ^ (q : ℝ) := by
    have hlocal' :
        ENNReal.ofReal (dist (f x) (f y)) ≤ ENNReal.ofReal (C i.1 * dist x y ^ (q : ℝ)) := by
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using
        hC i.1 x hxBall y hyBall
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hlocal'
  have hCi : C i.1 ≤ C₀ := Finset.le_sup i.2
  calc
    dist (f x) (f y) ≤ C i.1 * dist x y ^ (q : ℝ) := hlocal
    _ ≤ C₀ * dist x y ^ (q : ℝ) := by
          gcongr

/-- Helper for Exercise 21.1.1: on a compact metric space, positive local Hölder control upgrades
to a global Hölder estimate. -/
private lemma exists_holderWith_of_isCompactMetric
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {q : ℝ≥0} {f : X → Y}
    (hq : 0 < q)
    [CompactSpace X] :
    LocallyHolderWith q f → ∃ C : ℝ≥0, HolderWith C q f := by
  intro hf
  classical
  by_cases h_nonempty : Nonempty X
  · letI := h_nonempty
    have hcont : Continuous f := continuous_of_locallyHolderWithMetric hq hf
    obtain ⟨δ, hδpos, Cnear, hnear⟩ := exists_uniformLocalHolderBound_of_compactMetric hf
    let D : ℝ := Metric.diam (Set.range f)
    have hdiam : ∀ x y : X, dist (f x) (f y) ≤ D := by
      intro x y
      exact Metric.dist_le_diam_of_mem (isCompact_range hcont).isBounded ⟨x, rfl⟩ ⟨y, rfl⟩
    let Cfar : ℝ≥0 := ⟨D / δ ^ (q : ℝ), by positivity⟩
    refine ⟨max Cnear Cfar, ?_⟩
    intro x y
    -- Proof comment: nearby points use the uniform compactness estimate, while far points are
    -- controlled by the diameter of the compact image.
    by_cases hxy : dist x y < δ
    · have hlocal : dist (f x) (f y) ≤ max Cnear Cfar * dist x y ^ (q : ℝ) := by
        exact (hnear x y hxy).trans <| by
          gcongr
          exact le_max_left _ _
      have hlocal' :
          ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal (max Cnear Cfar * dist x y ^ (q : ℝ)) :=
        ENNReal.ofReal_le_ofReal hlocal
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using hlocal'
    · have hδle : δ ≤ dist x y := le_of_not_gt hxy
      have hδpow_pos : 0 < δ ^ (q : ℝ) := by
        positivity
      have hpow : δ ^ (q : ℝ) ≤ dist x y ^ (q : ℝ) := by
        gcongr
      have hfar : dist (f x) (f y) ≤ max Cnear Cfar * dist x y ^ (q : ℝ) := by
        calc
          dist (f x) (f y) ≤ D := hdiam x y
          _ = (D / δ ^ (q : ℝ)) * δ ^ (q : ℝ) := by
                field_simp [hδpow_pos.ne']
          _ ≤ (D / δ ^ (q : ℝ)) * dist x y ^ (q : ℝ) := by
                gcongr
          _ = Cfar * dist x y ^ (q : ℝ) := by
                simp [Cfar]
          _ ≤ max Cnear Cfar * dist x y ^ (q : ℝ) := by
                gcongr
                exact le_max_right _ _
      have hfar' :
          ENNReal.ofReal (dist (f x) (f y)) ≤
            ENNReal.ofReal (max Cnear Cfar * dist x y ^ (q : ℝ)) :=
        ENNReal.ofReal_le_ofReal hfar
      simpa [edist_dist, ENNReal.ofReal_mul, ENNReal.ofReal_rpow_of_nonneg] using hfar'
  · letI : IsEmpty X := ⟨fun x ↦ h_nonempty ⟨x⟩⟩
    exact ⟨0, HolderWith.of_isEmpty⟩

/-- Helper for Exercise 21.1.1: clip one real coordinate to the interval `[-T, T]`. -/
private noncomputable def clippedCubeCoordinate (T : ℝ≥0) (x : ℝ) : ℝ :=
  (Set.projIcc (-(T : ℝ)) (T : ℝ) (neg_le_self T.2) x : Set.Icc (-(T : ℝ)) (T : ℝ))

/-- Helper for Exercise 21.1.1: the clipped coordinate always belongs to `[-T, T]`. -/
private lemma clippedCubeCoordinate_mem_Icc (T : ℝ≥0) (x : ℝ) :
    clippedCubeCoordinate T x ∈ Set.Icc (-(T : ℝ)) (T : ℝ) := by
  -- Proof comment: `Set.projIcc` lands in the target interval by construction.
  exact (Set.projIcc (-(T : ℝ)) (T : ℝ) (neg_le_self T.2) x).2

/-- Helper for Exercise 21.1.1: coordinatewise clipping lands in the closed cube `[-T, T]^d`. -/
private lemma clipToEuclideanClosedCube_mem
    (T : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) :
    (WithLp.toLp 2 fun i : Fin d ↦ clippedCubeCoordinate T (x i)) ∈
      euclideanClosedCube d (T : ℝ) := by
  -- Proof comment: each coordinate was projected separately into `[-T, T]`.
  intro i
  simpa using clippedCubeCoordinate_mem_Icc T (x i)

/-- Helper for Exercise 21.1.1: clip an ambient Euclidean point coordinatewise into
`euclideanClosedCube d T`. -/
private noncomputable def clipToEuclideanClosedCube
    (T : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) :
    euclideanClosedCube d (T : ℝ) :=
  ⟨WithLp.toLp 2 fun i : Fin d ↦ clippedCubeCoordinate T (x i),
    clipToEuclideanClosedCube_mem (d := d) T x⟩

/-- Helper for Exercise 21.1.1: the clipped cube point has the expected coordinate formula. -/
private lemma clipToEuclideanClosedCube_apply
    (T : ℝ≥0) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (clipToEuclideanClosedCube (d := d) T x : EuclideanSpace ℝ (Fin d)) i =
      clippedCubeCoordinate T (x i) := by
  simp [clipToEuclideanClosedCube]

/-- Helper for Exercise 21.1.1: clipping fixes points that already lie in the closed cube. -/
private lemma clipToEuclideanClosedCube_eq_self
    {T : ℝ≥0} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ euclideanClosedCube d (T : ℝ)) :
    (clipToEuclideanClosedCube (d := d) T x : EuclideanSpace ℝ (Fin d)) = x := by
  -- Proof comment: on coordinates already lying in `[-T, T]`, `Set.projIcc` acts as the
  -- identity.
  ext i
  have hcoord :
      clippedCubeCoordinate T (x i) = x i := by
    unfold clippedCubeCoordinate
    exact congrArg Subtype.val <|
      Set.projIcc_of_mem (a := -(T : ℝ)) (b := (T : ℝ)) (h := neg_le_self T.2) (hx i)
  simpa [clipToEuclideanClosedCube_apply, hcoord]

/-- Helper for Exercise 21.1.1: the clipped ambient process agrees with the original process on
the cube. -/
private noncomputable def clippedCubeProcess
    (T : ℝ≥0)
    (X : EuclideanSpace ℝ (Fin d) → Ω → E) :
    EuclideanSpace ℝ (Fin d) → Ω → E :=
  fun x ω ↦ X (clipToEuclideanClosedCube (d := d) T x).1 ω

/-- Helper for Exercise 21.1.1: on cube points, the clipped ambient process is literally `X`. -/
private lemma clippedCubeProcess_eq_on_closedCube
    (T : ℝ≥0)
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∈ euclideanClosedCube d (T : ℝ)) :
    clippedCubeProcess (d := d) T X x = X x := by
  -- Proof comment: once `x` already belongs to the cube, the clipping map is the identity.
  funext ω
  simpa [clippedCubeProcess, clipToEuclideanClosedCube_eq_self (d := d) hx]

/-- Helper for Exercise 21.1.1: clipping one coordinate to `[-T, T]` is `1`-Lipschitz. -/
private lemma dist_clippedCubeCoordinate_le
    (T : ℝ≥0) (x y : ℝ) :
    dist (clippedCubeCoordinate T x) (clippedCubeCoordinate T y) ≤ dist x y := by
  have hprojLip :
      LipschitzWith 1 fun t : ℝ ↦ (Set.projIcc (-(T : ℝ)) (T : ℝ) (neg_le_self T.2) t : ℝ) := by
    -- Proof comment: projection to a closed interval is itself `1`-Lipschitz on `ℝ`.
    simpa using
      (LipschitzWith.projIcc (a := -(T : ℝ)) (b := T) (h := neg_le_self T.2))
  -- Proof comment: `clippedCubeCoordinate` is just that interval projection with the subtype
  -- coercion erased.
  simpa [clippedCubeCoordinate] using hprojLip.dist_le_mul x y

/-- Helper for Exercise 21.1.1: coordinatewise clipping into `[-T, T]^d` does not increase the
ambient Euclidean distance. -/
private lemma dist_clipToEuclideanClosedCube_le
    (T : ℝ≥0) (x y : EuclideanSpace ℝ (Fin d)) :
    dist
        ((clipToEuclideanClosedCube (d := d) T x : euclideanClosedCube d (T : ℝ)) :
          EuclideanSpace ℝ (Fin d))
        ((clipToEuclideanClosedCube (d := d) T y : euclideanClosedCube d (T : ℝ)) :
          EuclideanSpace ℝ (Fin d)) ≤
      dist x y := by
  let xT : euclideanClosedCube d (T : ℝ) := clipToEuclideanClosedCube (d := d) T x
  let yT : euclideanClosedCube d (T : ℝ) := clipToEuclideanClosedCube (d := d) T y
  have hcoord :
      ∀ i : Fin d,
        |((xT : EuclideanSpace ℝ (Fin d)) i) - ((yT : EuclideanSpace ℝ (Fin d)) i)| ≤
          |x i - y i| := by
    intro i
    -- Proof comment: each coordinate is clipped by a `1`-Lipschitz interval projection.
    simpa [xT, yT, clipToEuclideanClosedCube_apply, Real.dist_eq] using
      dist_clippedCubeCoordinate_le T (x i) (y i)
  have hsq :
      ‖((xT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) -
          ((yT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d))‖ ^ 2 ≤
        ‖x - y‖ ^ 2 := by
    calc
      ‖((xT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) -
          ((yT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d))‖ ^ 2
          =
            ∑ i : Fin d,
              ((((xT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) i) -
                (((yT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) i)) ^ 2 := by
              simpa [EuclideanSpace.real_norm_sq_eq]
      _ ≤ ∑ i : Fin d, (x i - y i) ^ 2 := by
            refine Finset.sum_le_sum ?_
            intro i _
            have hi := hcoord i
            have hi_sq :
                |((xT : EuclideanSpace ℝ (Fin d)) i) - ((yT : EuclideanSpace ℝ (Fin d)) i)| ^ 2 ≤
                  |x i - y i| ^ 2 := by
              exact sq_le_sq.mpr (by simpa using hi)
            simpa [sq_abs] using hi_sq
      _ = ‖x - y‖ ^ 2 := by
            simpa [EuclideanSpace.real_norm_sq_eq]
  have hnorm :
      ‖((xT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) -
          ((yT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d))‖ ≤
        ‖x - y‖ := by
    nlinarith [norm_nonneg
      (((xT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d)) -
        ((yT : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin d))),
      norm_nonneg (x - y), hsq]
  simpa [dist_eq_norm, xT, yT] using hnorm

/-- Helper for Exercise 21.1.1: the corresponding `edist` estimate is the form consumed by the
Kolmogorov owner API. -/
private lemma edist_clipToEuclideanClosedCube_le
    (T : ℝ≥0) (x y : EuclideanSpace ℝ (Fin d)) :
    edist
        ((clipToEuclideanClosedCube (d := d) T x : euclideanClosedCube d (T : ℝ)) :
          EuclideanSpace ℝ (Fin d))
        ((clipToEuclideanClosedCube (d := d) T y : euclideanClosedCube d (T : ℝ)) :
          EuclideanSpace ℝ (Fin d)) ≤
      edist x y := by
  -- Proof comment: convert the metric contraction into the extended-distance inequality used by
  -- `IsKolmogorovProcess`.
  simpa [edist_dist] using
    ENNReal.ofReal_le_ofReal (dist_clipToEuclideanClosedCube_le (d := d) T x y)

/-- Helper for Exercise 21.1.1: clipping the ambient process into one fixed cube preserves the
Kolmogorov owner on every larger ambient cube. -/
private theorem isKolmogorovProcessOnEuclideanClosedCube_clippedCubeProcess
    (μ : Measure Ω)
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β T C : ℝ≥0}
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (R : ℝ≥0) :
    IsKolmogorovProcessOnEuclideanClosedCube μ (clippedCubeProcess (d := d) T X) R α β C := by
  refine
    { measurablePair := ?_
      kolmogorovCondition := ?_
      p_pos := hC.p_pos
      q_pos := hC.q_pos }
  · intro s t
    -- Proof comment: every clipped point lands back in the original cube, so the pair
    -- measurability is read directly from the original cube owner.
    simpa [clippedCubeProcess] using
      hC.measurablePair
        (clipToEuclideanClosedCube (d := d) T s.1)
        (clipToEuclideanClosedCube (d := d) T t.1)
  · intro s t
    have hclip :
        edist
            (((clipToEuclideanClosedCube (d := d) T s.1 : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d)))
            (((clipToEuclideanClosedCube (d := d) T t.1 : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))) ≤ edist s t := by
      simpa using edist_clipToEuclideanClosedCube_le (d := d) T s.1 t.1
    have hclip_pow :
        edist
            (((clipToEuclideanClosedCube (d := d) T s.1 : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d)))
            (((clipToEuclideanClosedCube (d := d) T t.1 : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))) ^
          (((d : ℝ≥0) : ℝ) + β) ≤
          edist s t ^ (((d : ℝ≥0) : ℝ) + β) :=
      ENNReal.rpow_le_rpow hclip (by positivity)
    -- Proof comment: the original increment bound is applied at the clipped endpoints, and the
    -- contraction of the clipping map transports the right-hand side back to the larger cube.
    calc
      ∫⁻ ω,
          edist
              ((clippedCubeProcess (d := d) T X) s ω)
              ((clippedCubeProcess (d := d) T X) t ω) ^ (α : ℝ) ∂μ
          ≤
            (C : ℝ≥0∞) *
              edist
                (((clipToEuclideanClosedCube (d := d) T s.1 :
                    euclideanClosedCube d (T : ℝ)) :
                    EuclideanSpace ℝ (Fin d)))
                (((clipToEuclideanClosedCube (d := d) T t.1 :
                    euclideanClosedCube d (T : ℝ)) :
                    EuclideanSpace ℝ (Fin d))) ^ (((d : ℝ≥0) : ℝ) + β) := by
              simpa [clippedCubeProcess] using
                IsKolmogorovProcessOnEuclideanClosedCube.increment_lintegral_le
                  (d := d)
                  (μ := μ)
                  (X := X)
                  (T := T)
                  (α := α)
                  (β := β)
                  (C := C)
                  hC
                  (s := ((clipToEuclideanClosedCube (d := d) T t.1 :
                    euclideanClosedCube d (T : ℝ)) : EuclideanSpace ℝ (Fin d)))
                  (t := ((clipToEuclideanClosedCube (d := d) T s.1 :
                    euclideanClosedCube d (T : ℝ)) : EuclideanSpace ℝ (Fin d)))
                  (clipToEuclideanClosedCube_mem (d := d) T t.1)
                  (clipToEuclideanClosedCube_mem (d := d) T s.1)
      _ ≤ (C : ℝ≥0∞) * edist s t ^ (((d : ℝ≥0) : ℝ) + β) := by
            gcongr

/-- Helper for Exercise 21.1.1: restricting an ambient locally Hölder map to the closed-cube
subtype preserves local Hölder control. -/
private lemma locallyHolderWith_restrict_euclideanClosedCube
    {T γ : ℝ≥0} {f : EuclideanSpace ℝ (Fin d) → E}
    (hf : LocallyHolderWith γ f) :
    LocallyHolderWith γ (fun t : euclideanClosedCube d (T : ℝ) ↦ f t.1) := by
  intro t
  rcases hf t.1 with ⟨s, hs, C, hC⟩
  -- Proof comment: pull the ambient neighborhood back along the subtype inclusion and reuse the
  -- same Hölder estimate on the restricted set.
  refine ⟨Subtype.val ⁻¹' s, ?_, C, ?_⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hs
  · intro u hu v hv
    simpa using hC u.1 hu v.1 hv

/-- Helper for Exercise 21.1.1: ambient locally Hölder sample paths restrict to locally Hölder
sample paths on every closed cube. -/
private lemma hasLocallyHolderPaths_restrict_euclideanClosedCube
    {T γ : ℝ≥0}
    {Y : EuclideanSpace ℝ (Fin d) → Ω → E}
    (hY : HasLocallyHolderPaths (d := d) γ Y) :
    ∀ ω : Ω,
      LocallyHolderWith γ
        (fun t : euclideanClosedCube d (T : ℝ) ↦ Y t.1 ω) := by
  intro ω
  exact
    locallyHolderWith_restrict_euclideanClosedCube
      (d := d)
      (T := T)
      (γ := γ)
      (f := fun x ↦ Y x ω)
      (hY ω)

/-- Helper for Exercise 21.1.1: the source-facing Kolmogorov condition on `[0,T]`, kept local so
the cube proof can reuse the one-dimensional owner shape without importing non-`module` files. -/
private def IsKolmogorovProcessOnIcc
    (μ : Measure Ω) (X : NNReal → Ω → E) (T α β C : ℝ≥0) : Prop :=
  0 < α ∧
    0 < β ∧
      IsKolmogorovProcess (fun t : Set.Icc (0 : NNReal) T ↦ X t) μ (α : ℝ) (1 + (β : ℝ)) C

/-- Helper for Exercise 21.1.1: the interval owner records positivity of the moment exponent. -/
private theorem IsKolmogorovProcessOnIcc.alpha_pos
    {μ : Measure Ω} {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    0 < α := by
  -- Proof comment: the positivity requirement is stored explicitly in the theorem-local owner.
  exact h.1

/-- Helper for Exercise 21.1.1: the interval owner records positivity of the spatial exponent. -/
private theorem IsKolmogorovProcessOnIcc.beta_pos
    {μ : Measure Ω} {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    0 < β := by
  -- Proof comment: the interval owner stores the positive gap parameter separately from the
  -- canonical Kolmogorov owner.
  exact h.2.1

/-- Helper for Exercise 21.1.1: unwrap the theorem-local interval owner to the canonical
`IsKolmogorovProcess` statement on the interval subtype. -/
private theorem IsKolmogorovProcessOnIcc.isKolmogorovProcess
    {μ : Measure Ω} {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C) :
    IsKolmogorovProcess (fun t : Set.Icc (0 : NNReal) T ↦ X t) μ (α : ℝ) (1 + (β : ℝ)) C := by
  -- Proof comment: only the canonical mathlib owner is used in later measurability and increment
  -- estimates.
  exact h.2.2

/-- Helper for Exercise 21.1.1: a one-dimensional interval owner gives the ambient-point increment
estimate on `[0,T]`. -/
private theorem IsKolmogorovProcessOnIcc.increment_lintegral_le
    {μ : Measure Ω} {X : NNReal → Ω → E} {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    {s t : NNReal} (hs : s ≤ T) (ht : t ≤ T) :
    ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
      (C : ℝ≥0∞) * edist t s ^ (1 + (β : ℝ)) := by
  have hs' : s ∈ Set.Icc (0 : NNReal) T := by
    simpa using hs
  have ht' : t ∈ Set.Icc (0 : NNReal) T := by
    simpa using ht
  -- Proof comment: the interval owner is already the restricted Kolmogorov process on
  -- `Set.Icc (0, T)`, so the desired estimate is just the owner inequality on subtype points.
  simpa [edist_comm] using h.2.2.kolmogorovCondition ⟨s, hs'⟩ ⟨t, ht'⟩

/-- Helper for Exercise 21.1.1: the local dyadic cutoff for the translated interval `[0, 2T]`. -/
private noncomputable def dyadicCutoff (T : ℝ≥0) (n : ℕ) : ℕ :=
  Nat.ceil (T : ℝ) * 2 ^ n

/-- Helper for Exercise 21.1.1: the `k`-th clipped dyadic point on `[0,T]`. -/
private noncomputable def dyadicPointUpTo (T : ℝ≥0) (n k : ℕ) : NNReal :=
  min T ((k : NNReal) / (2 : NNReal) ^ n)

/-- Helper for Exercise 21.1.1: every local dyadic point lies in the interval `[0,T]`. -/
private lemma dyadicPointUpTo_mem_Icc (T : ℝ≥0) (n k : ℕ) :
    dyadicPointUpTo T n k ∈ Set.Icc (0 : NNReal) T := by
  constructor
  · positivity
  · exact min_le_left _ _

/-- Helper for Exercise 21.1.1: a row-`n` coordinate fiber freezes every coordinate except `i`
at translated dyadic anchor points from `[0, 2T]`, including the terminal anchor `2T`. -/
private abbrev cubeFiberAnchor (T : ℝ≥0) (n : ℕ) (i : Fin d) :=
  {j : Fin d // j ≠ i} → Fin (dyadicCutoff (2 * T) n + 1)

/-- Helper for Exercise 21.1.1: the fixed anchor vector for a row-`n` coordinate fiber uses `0`
in the varying coordinate and translated dyadic anchor values elsewhere. -/
private noncomputable def cubeFiberBase
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun j : Fin d =>
    if h : j = i then
      0
    else
      ((dyadicPointUpTo (2 * T) n (a ⟨j, h⟩) : NNReal) : ℝ) - T

/-- Helper for Exercise 21.1.1: a coordinate fiber point is obtained from the anchor vector by
varying only the `i`-th coordinate through the translated interval `[0, 2T] - T = [-T, T]`. -/
private noncomputable def cubeFiberPoint
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i) (u : NNReal) :
    euclideanClosedCube d (T : ℝ) :=
  ⟨cubeFiberBase (d := d) T n i a +
      EuclideanSpace.single i (((min (2 * T) u : NNReal) : ℝ) - T), by
    intro j
    by_cases hj : j = i
    · subst hj
      have hcoord :
          (cubeFiberBase (d := d) T n j a +
              EuclideanSpace.single j (((min (2 * T) u : NNReal) : ℝ) - T)) j =
            (((min (2 * T) u : NNReal) : ℝ) - T) := by
        simp [cubeFiberBase]
      have hmin_nonneg : (0 : ℝ) ≤ ((min (2 * T) u : NNReal) : ℝ) := by
        positivity
      have hmin_le : ((min (2 * T) u : NNReal) : ℝ) ≤ (2 : ℝ) * T := by
        exact_mod_cast min_le_left (2 * T) u
      -- Proof comment: the varying coordinate is clipped to `[0, 2T]`, so translating by `-T`
      -- lands exactly in `[-T, T]`.
      rw [hcoord]
      constructor <;> linarith
    · have hanchor :
          dyadicPointUpTo (2 * T) n (a ⟨j, hj⟩) ∈ Set.Icc (0 : NNReal) (2 * T) :=
        dyadicPointUpTo_mem_Icc (2 * T) n (a ⟨j, hj⟩)
      have hcoord :
          (cubeFiberBase (d := d) T n i a +
              EuclideanSpace.single i (((min (2 * T) u : NNReal) : ℝ) - T)) j =
            ((dyadicPointUpTo (2 * T) n (a ⟨j, hj⟩) : NNReal) : ℝ) - T := by
        simp [cubeFiberBase, hj]
      have hanchor_nonneg : (0 : ℝ) ≤
          ((dyadicPointUpTo (2 * T) n (a ⟨j, hj⟩) : NNReal) : ℝ) := by
        exact_mod_cast hanchor.1
      have hanchor_le : ((dyadicPointUpTo (2 * T) n (a ⟨j, hj⟩) : NNReal) : ℝ) ≤
          (2 : ℝ) * T := by
        exact_mod_cast hanchor.2
      -- Proof comment: the frozen anchor coordinates come from the same translated interval
      -- `[0, 2T]`, so the same shift argument places them in `[-T, T]`.
      rw [hcoord]
      constructor <;> linarith⟩

/-- Helper for Exercise 21.1.1: the anchor vector contributes `0` in the varying coordinate. -/
private lemma cubeFiberBase_apply_same
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i) :
    cubeFiberBase (d := d) T n i a i = 0 := by
  simp [cubeFiberBase]

/-- Helper for Exercise 21.1.1: away from the varying coordinate, the fiber base records the
translated dyadic anchor values. -/
private lemma cubeFiberBase_apply_ne
    (T : ℝ≥0) (n : ℕ) (i j : Fin d) (a : cubeFiberAnchor (d := d) T n i) (hj : j ≠ i) :
    cubeFiberBase (d := d) T n i a j =
      ((dyadicPointUpTo (2 * T) n (a ⟨j, hj⟩) : NNReal) : ℝ) - T := by
  simp [cubeFiberBase, hj]

/-- Helper for Exercise 21.1.1: on the varying coordinate, a fiber point is just the translated
clipped interval parameter. -/
private lemma cubeFiberPoint_apply_same
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i) (u : NNReal) :
    (cubeFiberPoint (d := d) T n i a u : EuclideanSpace ℝ (Fin d)) i =
      (((min (2 * T) u : NNReal) : ℝ) - T) := by
  simp [cubeFiberPoint, cubeFiberBase]

/-- Helper for Exercise 21.1.1: away from the varying coordinate, a fiber point keeps the fixed
translated dyadic anchor value. -/
private lemma cubeFiberPoint_apply_ne
    (T : ℝ≥0) (n : ℕ) (i j : Fin d) (a : cubeFiberAnchor (d := d) T n i) (u : NNReal)
    (hj : j ≠ i) :
    (cubeFiberPoint (d := d) T n i a u : EuclideanSpace ℝ (Fin d)) j =
      ((dyadicPointUpTo (2 * T) n (a ⟨j, hj⟩) : NNReal) : ℝ) - T := by
  simp [cubeFiberPoint, cubeFiberBase, hj]

/-- Helper for Exercise 21.1.1: on the true interval `[0, 2T]`, the fiber point is a translated
single-coordinate perturbation of the fixed anchor vector. -/
private lemma cubeFiberPoint_eq_base_add_single
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i)
    (u : Set.Icc (0 : NNReal) (2 * T)) :
    ((cubeFiberPoint (d := d) T n i a u.1 : euclideanClosedCube d (T : ℝ)) :
        EuclideanSpace ℝ (Fin d)) =
      cubeFiberBase (d := d) T n i a + EuclideanSpace.single i (((u : NNReal) : ℝ) - T) := by
  ext j
  by_cases hj : j = i
  · subst hj
    have hu : min (2 * T) (u : NNReal) = (u : NNReal) := min_eq_right u.2.2
    simp [cubeFiberPoint, cubeFiberBase, hu]
  · have hu : min (2 * T) (u : NNReal) = (u : NNReal) := min_eq_right u.2.2
    simp [cubeFiberPoint, cubeFiberBase, hj, hu]

/-- Helper for Exercise 21.1.1: along one coordinate fiber, the ambient Euclidean distance is
exactly the interval distance in the varying parameter. -/
private lemma dist_cubeFiberPoint_eq
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i)
    (s t : Set.Icc (0 : NNReal) (2 * T)) :
    dist
        (((cubeFiberPoint (d := d) T n i a s.1 : euclideanClosedCube d (T : ℝ)) :
            EuclideanSpace ℝ (Fin d)))
        (((cubeFiberPoint (d := d) T n i a t.1 : euclideanClosedCube d (T : ℝ)) :
            EuclideanSpace ℝ (Fin d))) =
      dist s t := by
  -- Proof comment: translating by the fixed anchor vector does not change distance, and only one
  -- Euclidean coordinate varies along the fiber.
  calc
    dist
        (((cubeFiberPoint (d := d) T n i a s.1 : euclideanClosedCube d (T : ℝ)) :
            EuclideanSpace ℝ (Fin d)))
        (((cubeFiberPoint (d := d) T n i a t.1 : euclideanClosedCube d (T : ℝ)) :
            EuclideanSpace ℝ (Fin d))) =
      dist
        (EuclideanSpace.single i (((s : NNReal) : ℝ) - T))
        (EuclideanSpace.single i (((t : NNReal) : ℝ) - T)) := by
          rw [cubeFiberPoint_eq_base_add_single (d := d) T n i a s,
            cubeFiberPoint_eq_base_add_single (d := d) T n i a t, dist_add_left]
    _ = dist (((s : NNReal) : ℝ) - T) (((t : NNReal) : ℝ) - T) := by
          simpa using
            EuclideanSpace.dist_single_same i (((s : NNReal) : ℝ) - T) (((t : NNReal) : ℝ) - T)
    _ = dist ((s : NNReal) : ℝ) ((t : NNReal) : ℝ) := by
          simpa [sub_eq_add_neg] using dist_add_right ((s : NNReal) : ℝ) ((t : NNReal) : ℝ) (-(T : ℝ))
    _ = dist s t := by
          rfl

/-- Helper for Exercise 21.1.1: the corresponding `edist` identity is the form consumed by the
Kolmogorov owner API. -/
private lemma edist_cubeFiberPoint_eq
    (T : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i)
    (s t : Set.Icc (0 : NNReal) (2 * T)) :
    edist
        (((cubeFiberPoint (d := d) T n i a s.1 : euclideanClosedCube d (T : ℝ)) :
            EuclideanSpace ℝ (Fin d)))
        (((cubeFiberPoint (d := d) T n i a t.1 : euclideanClosedCube d (T : ℝ)) :
            EuclideanSpace ℝ (Fin d))) =
      edist s t := by
  simpa [edist_dist] using congrArg ENNReal.ofReal (dist_cubeFiberPoint_eq (d := d) T n i a s t)

/-- Helper for Exercise 21.1.1: the interval exponent on one coordinate fiber is
`1 + ((d - 1) + β) = d + β`. -/
private lemma cubeFiberExponent_eq
    (i : Fin d) {β : ℝ≥0} :
    (((d : ℝ≥0) + β : ℝ≥0) : ℝ) =
      1 + ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ≥0) : ℝ) := by
  have hd : 0 < d := Fin.pos i
  have hd' : d = (d - 1) + 1 := by
    simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hd).symm
  have hcast : (d : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast hd'
  change (d : ℝ) + (β : ℝ) = 1 + (((d - 1 : ℕ) : ℝ) + (β : ℝ))
  rw [hcast]
  ring

/-- Helper for Exercise 21.1.1: a translated coordinate fiber of the cube owner satisfies the
one-dimensional Kolmogorov condition with exponent parameter `(d - 1) + β`. -/
private theorem cubeFiberProcess_isKolmogorovProcessOnIcc
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β T C : ℝ≥0}
    (hβ : 0 < β)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i) :
    IsKolmogorovProcessOnIcc μ
      (fun u ω ↦ X (cubeFiberPoint (d := d) T n i a u).1 ω)
      (2 * T) α (((d - 1 : ℕ) : ℝ≥0) + β) C := by
  refine ⟨hC.p_pos, add_pos_of_nonneg_of_pos (by positivity) hβ, ?_⟩
  refine
    { measurablePair := ?_
      kolmogorovCondition := ?_
      p_pos := hC.p_pos
      q_pos := by positivity }
  · intro s t
    -- Proof comment: on each fixed fiber, measurability is inherited by evaluating the cube owner
    -- at two fixed cube points.
    simpa using
      hC.measurablePair
        (cubeFiberPoint (d := d) T n i a s.1)
        (cubeFiberPoint (d := d) T n i a t.1)
  · intro s t
    -- Proof comment: the cube owner controls the two fiber points, and the fiber geometry reduces
    -- the ambient distance back to the interval distance in the varying coordinate.
    change
      ∫⁻ ω, edist (X (cubeFiberPoint (d := d) T n i a s.1).1 ω)
            (X (cubeFiberPoint (d := d) T n i a t.1).1 ω) ^ (α : ℝ) ∂μ ≤
        (C : ℝ≥0∞) * edist s t ^ (1 + ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))
    calc
      ∫⁻ ω, edist (X (cubeFiberPoint (d := d) T n i a s.1).1 ω)
            (X (cubeFiberPoint (d := d) T n i a t.1).1 ω) ^ (α : ℝ) ∂μ
          ≤
            (C : ℝ≥0∞) *
              edist
                (((cubeFiberPoint (d := d) T n i a s.1 : euclideanClosedCube d (T : ℝ)) :
                    EuclideanSpace ℝ (Fin d)))
                (((cubeFiberPoint (d := d) T n i a t.1 : euclideanClosedCube d (T : ℝ)) :
                    EuclideanSpace ℝ (Fin d))) ^
                (((d : ℝ≥0) + β : ℝ)) := by
              simpa using
                hC.increment_lintegral_le
                  (s := (cubeFiberPoint (d := d) T n i a t.1).1)
                  (t := (cubeFiberPoint (d := d) T n i a s.1).1)
                  (cubeFiberPoint (d := d) T n i a t.1).2
                  (cubeFiberPoint (d := d) T n i a s.1).2
      _ =
          (C : ℝ≥0∞) * edist s t ^ ((((d : ℝ≥0) : ℝ) + β)) := by
            rw [edist_cubeFiberPoint_eq (d := d) T n i a s t]
      _ =
          (C : ℝ≥0∞) * edist s t ^ (1 + ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ))) := by
            congr 2
            have hd : (d : ℝ) = ((d - 1 : ℕ) : ℝ) + 1 := by
              have hdNat : d = (d - 1) + 1 := by
                simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos (Fin.pos i)).symm
              exact_mod_cast hdNat
            change (d : ℝ) + (β : ℝ) = 1 + (((d - 1 : ℕ) : ℝ) + (β : ℝ))
            rw [hd]
            ring
/-- Helper for Exercise 21.1.1: the ceiling dyadic approximation `⌈2^n t⌉ / 2^n` on
`ℝ≥0`. -/
private noncomputable def rightDyadicApprox (t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n

/-- Helper for Exercise 21.1.1: the ceiling dyadic approximants converge back to the target
nonnegative real. -/
private lemma tendsto_rightDyadicApprox (t : ℝ≥0) :
    Filter.Tendsto (rightDyadicApprox t) Filter.atTop (nhds t) := by
  -- Proof comment: this is the standard `⌈2^n t⌉ / 2^n → t` limit on the dyadic mesh.
  refine (NNReal.tendsto_coe).mp ?_
  simpa [rightDyadicApprox] using
    (tendsto_nat_ceil_mul_div_atTop (a := (t : ℝ)) t.2).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)

/-- Helper for Exercise 21.1.1: clip the dyadic ceiling approximation back to the fixed horizon
`T`. -/
private noncomputable def clippedRightDyadicApprox (T t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  min T (rightDyadicApprox t n)

/-- Helper for Exercise 21.1.1: the clipped dyadic ceiling approximation always stays in
`[0, T]`. -/
private lemma clippedRightDyadicApprox_mem_Icc (T t : ℝ≥0) (n : ℕ) :
    clippedRightDyadicApprox T t n ∈ Set.Icc (0 : ℝ≥0) T := by
  constructor
  · exact bot_le
  · exact min_le_left _ _

/-- Helper for Exercise 21.1.1: if the target lies below the horizon, the clipped dyadic ceiling
approximants still converge to that target. -/
private lemma tendsto_clippedRightDyadicApprox {t T : ℝ≥0} (htT : t ≤ T) :
    Filter.Tendsto (clippedRightDyadicApprox T t) Filter.atTop (nhds t) := by
  have hmin :
      Filter.Tendsto (fun x : ℝ≥0 ↦ min T x) (nhds t) (nhds (min T t)) :=
    (continuous_const.min continuous_id).continuousAt.tendsto
  have hclip :
      Filter.Tendsto (fun n ↦ min T (rightDyadicApprox t n)) Filter.atTop (nhds (min T t)) :=
    hmin.comp (tendsto_rightDyadicApprox t)
  -- Proof comment: clipping by `min T` is continuous, and at the target point the clipping is
  -- inactive because `t ≤ T`.
  simpa [clippedRightDyadicApprox, min_eq_right htT] using hclip

/-- Helper for Exercise 21.1.1: use the theorem-21.6 spelling `intervalClippedDyadicApprox` for
the clipped right-dyadic approximation on one interval fiber. -/
private abbrev intervalClippedDyadicApprox (T t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  clippedRightDyadicApprox T t n

/-- Helper for Exercise 21.1.1: the deterministic cutoff index lands at the terminal time `T`. -/
private lemma dyadicPointUpTo_cutoff (T : ℝ≥0) (n : ℕ) :
    dyadicPointUpTo T n (dyadicCutoff T n) = T := by
  -- Proof comment: at the cutoff index the unclipped dyadic time is already beyond `T`, so the
  -- outer `min T` collapses to `T`.
  unfold dyadicPointUpTo dyadicCutoff
  apply min_eq_left
  have hceil : T ≤ (Nat.ceil (T : ℝ) : ℝ≥0) := by
    exact_mod_cast Nat.le_ceil (T : ℝ)
  have hpow_ne : (2 : ℝ≥0) ^ n ≠ 0 := by
    positivity
  have hcutoff :
      ((Nat.ceil (T : ℝ) * 2 ^ n : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n =
        (Nat.ceil (T : ℝ) : ℝ≥0) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (mul_div_cancel₀ (Nat.ceil (T : ℝ) : ℝ≥0) hpow_ne)
  calc
    T ≤ (Nat.ceil (T : ℝ) : ℝ≥0) := hceil
    _ = ((Nat.ceil (T : ℝ) * 2 ^ n : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n := hcutoff.symm

/-- Helper for Exercise 21.1.1: refining the dyadic mesh preserves coarse row values at even
indices. -/
private lemma dyadicPointUpTo_even (T : ℝ≥0) (n k : ℕ) :
    dyadicPointUpTo T (n + 1) (2 * k) = dyadicPointUpTo T n k := by
  -- Proof comment: doubling the row index compensates exactly for the extra factor of `2` in the
  -- refined mesh denominator.
  unfold dyadicPointUpTo
  have htwo : (2 : ℝ≥0) ≠ 0 := by
    positivity
  calc
    min T (((2 * k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ (n + 1))
        = min T (((k : ℝ≥0) * 2) / ((2 : ℝ≥0) ^ n * 2)) := by
            simp [Nat.cast_mul, pow_succ, mul_comm]
    _ = min T ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) := by
          rw [mul_div_mul_right _ _ htwo]

/-- Helper for Exercise 21.1.1: any coarse dyadic row sample reappears on a finer row after the
obvious index rescaling. -/
private lemma dyadicPointUpTo_refine
    (T : ℝ≥0) (m r k : ℕ) :
    dyadicPointUpTo T (m + r) (k * 2 ^ r) = dyadicPointUpTo T m k := by
  induction r generalizing k with
  | zero =>
      -- Proof comment: no refinement means there is nothing to prove.
      simp [dyadicPointUpTo]
  | succ r ihr =>
      -- Proof comment: peel off one refinement step and use the even-index compatibility.
      calc
        dyadicPointUpTo T (m + r.succ) (k * 2 ^ r.succ)
            = dyadicPointUpTo T ((m + r) + 1) (2 * (k * 2 ^ r)) := by
                have hk :
                    k * 2 ^ r.succ = 2 * (k * 2 ^ r) := by
                  simp [pow_succ, Nat.mul_left_comm, Nat.mul_comm]
                rw [hk, Nat.add_assoc]
        _ = dyadicPointUpTo T (m + r) (k * 2 ^ r) := by
              simpa using dyadicPointUpTo_even T (m + r) (k * 2 ^ r)
        _ = dyadicPointUpTo T m k := ihr k

/-- Helper for Exercise 21.1.1: the right-dyadic ceil index stays below the deterministic cutoff
on any interval containing the target time. -/
private lemma dyadicRightApprox_index_le_cutoff {t T : ℝ≥0} (htT : t ≤ T) (n : ℕ) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ≤ dyadicCutoff T n := by
  -- Proof comment: once `t ≤ T ≤ ⌈T⌉`, scaling by `2^n` keeps the ceil index below the cutoff.
  unfold dyadicCutoff
  refine Nat.ceil_le.mpr ?_
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  calc
    (t : ℝ) * (2 : ℝ) ^ n ≤ (T : ℝ) * (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast htT) hpow_nonneg
    _ ≤ (Nat.ceil (T : ℝ) : ℝ) * (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (Nat.le_ceil (T : ℝ)) hpow_nonneg
    _ = ((Nat.ceil (T : ℝ) * 2 ^ n : ℕ) : ℝ) := by
      simp [Nat.cast_mul, Nat.cast_pow]

/-- Helper for Exercise 21.1.1: the dyadic row threshold for exponent `q` is the mesh size
`2^(-q n)`. -/
private noncomputable def intervalDyadicStepThreshold (q : ℝ≥0) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((q : ℝ) * n))

/-- Helper for Exercise 21.1.1: the row-`n` bad event on one interval fiber records that some
adjacent clipped dyadic increment exceeds the threshold `2^(-q n)`. -/
private def intervalDyadicRowBadEvent
    (X : ℝ≥0 → Ω → E) (T q : ℝ≥0) (n : ℕ) : Set Ω :=
  {ω | ∃ k < dyadicCutoff T n,
      intervalDyadicStepThreshold q n <
        dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω)}

/-- Helper for Exercise 21.1.1: outside the row bad event, every adjacent row increment is
bounded by the dyadic threshold. -/
private lemma dist_le_intervalDyadicStepThreshold_of_notMem_intervalDyadicRowBadEvent
    {X : ℝ≥0 → Ω → E} {T q : ℝ≥0} {n k : ℕ} {ω : Ω}
    (hgood : ω ∉ intervalDyadicRowBadEvent X T q n)
    (hk : k < dyadicCutoff T n) :
    dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω) ≤
      intervalDyadicStepThreshold q n := by
  -- Proof comment: a larger adjacent increment would give a direct witness that `ω` lies in the
  -- bad event.
  by_contra hdist
  exact hgood ⟨k, hk, lt_of_not_ge hdist⟩

/-- Helper for Exercise 21.1.1: adjacent points on a clipped dyadic row are separated by at most
one mesh size `2^{-n}`. -/
private lemma dist_dyadicPointUpTo_succ_le_mesh (T : ℝ≥0) (n k : ℕ) :
    dist (dyadicPointUpTo T n (k + 1)) (dyadicPointUpTo T n k) ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
  have hmin :
      |min (T : ℝ) ((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
          min (T : ℝ) ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)| ≤
        |((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
          ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)| := by
    calc
      |min (T : ℝ) ((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
          min (T : ℝ) ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)|
          ≤ max
              |(T : ℝ) - (T : ℝ)|
              |((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
                ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)| := by
              simpa using
                abs_min_sub_min_le_max
                  (T : ℝ)
                  ((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
                  (T : ℝ)
                  ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)
      _ = |((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
            ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ)| := by
            simp
  have hraw_eq :
      ((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
          ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) =
        (1 : ℝ) / (2 : ℝ) ^ n := by
    norm_num [Nat.cast_add, Nat.cast_one, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow]
    ring
  have hraw_nonneg :
      0 ≤
        ((((k + 1 : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) -
          ((((k : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n : ℝ≥0) : ℝ) := by
    rw [hraw_eq]
    positivity
  -- Proof comment: clipping by `min T` is 1-Lipschitz, so the clipped row increment is bounded
  -- by the underlying dyadic mesh size.
  rw [NNReal.dist_eq]
  exact (hmin.trans_eq <| by rw [abs_of_nonneg hraw_nonneg, hraw_eq])

/-- Helper for Exercise 21.1.1: the refined right-dyadic index is either the doubled coarse index
or the immediately preceding refined index. -/
private lemma refinedDyadicApproxIndices_adjacent (t : ℝ≥0) (n : ℕ) :
    let j := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
    let j' := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1))
    j' ≤ 2 * j ∧ 2 * j ≤ j' + 1 := by
  let x : ℝ := (t : ℝ) * (2 : ℝ) ^ n
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hrefine :
      ((t : ℝ) * (2 : ℝ) ^ (n + 1)) = 2 * x := by
    -- Proof comment: passing from row `n` to row `n+1` simply doubles the scaled parameter.
    dsimp [x]
    rw [pow_succ]
    ring
  constructor
  · rw [hrefine]
    refine Nat.ceil_le.2 ?_
    calc
      2 * x ≤ 2 * (Nat.ceil x : ℝ) := by
        gcongr
        exact Nat.le_ceil x
      _ = ((2 * Nat.ceil x : ℕ) : ℝ) := by norm_num
  · rw [hrefine]
    have hceil_lt : ((Nat.ceil x : ℝ)) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
    have hdouble_lt :
        (2 * (Nat.ceil x : ℝ)) < (Nat.ceil (2 * x) : ℝ) + 2 := by
      have hleft : (2 * (Nat.ceil x : ℝ)) < 2 * x + 2 := by
        nlinarith
      have hright : 2 * x + 2 ≤ (Nat.ceil (2 * x) : ℝ) + 2 := by
        gcongr
        exact Nat.le_ceil (2 * x)
      exact lt_of_lt_of_le hleft hright
    have hdouble_nat : 2 * Nat.ceil x < Nat.ceil (2 * x) + 2 := by
      exact_mod_cast hdouble_lt
    have hsucc : 2 * Nat.ceil x < (Nat.ceil (2 * x) + 1).succ := by
      simpa [Nat.add_assoc] using hdouble_nat
    exact Nat.lt_succ_iff.mp hsucc

/-- Helper for Exercise 21.1.1: if two interval times are ordered and within one mesh, then their
right-dyadic row indices differ by at most one. -/
private lemma dyadicApproxIndices_adjacent_of_dist_le
    {s t : ℝ≥0} {n : ℕ}
    (hst : s ≤ t)
    (hclose : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n) :
    Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) ≤ Nat.ceil ((s : ℝ) * (2 : ℝ) ^ n) + 1 := by
  have hpow_nonneg : 0 ≤ (2 : ℝ) ^ n := by
    positivity
  have hst_real : (s : ℝ) ≤ t := by
    exact_mod_cast hst
  have hdist_eq : dist s t = (t : ℝ) - s := by
    rw [NNReal.dist_eq, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr hst_real
  have hsub_le : (t : ℝ) - s ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    simpa [hdist_eq] using hclose
  have hmul_le : (t : ℝ) * (2 : ℝ) ^ n ≤ (s : ℝ) * (2 : ℝ) ^ n + 1 := by
    have hscaled := mul_le_mul_of_nonneg_right hsub_le hpow_nonneg
    have hpow_pos : 0 < (2 : ℝ) ^ n := by positivity
    have hpow_ne : (2 : ℝ) ^ n ≠ 0 := hpow_pos.ne'
    have hunit : ((1 : ℝ) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n = 1 := by
      field_simp [hpow_ne]
    have hscaled' : ((t : ℝ) - s) * (2 : ℝ) ^ n ≤ 1 := by
      simpa [hunit] using hscaled
    nlinarith
  -- Proof comment: after scaling by `2^n`, a one-mesh interval gap becomes a difference of at
  -- most `1`, which forces the ceiling indices to be adjacent.
  have hs_nonneg : 0 ≤ (s : ℝ) * (2 : ℝ) ^ n := by positivity
  exact le_trans (Nat.ceil_mono hmul_le) <| by
    simpa using (Nat.ceil_add_natCast hs_nonneg 1).le

/-- Helper for Exercise 21.1.1: on a good dyadic row, two clipped approximants within one mesh
are separated by at most one threshold jump. -/
private lemma intervalClippedDyadicApprox_pair_le_of_rowGood_of_dist_le
    {X : ℝ≥0 → Ω → E} {T q : ℝ≥0} {s t : ℝ≥0} {n : ℕ} {ω : Ω}
    (hsT : s ≤ T)
    (htT : t ≤ T)
    (hst : s ≤ t)
    (hclose : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n)
    (hgood : ω ∉ intervalDyadicRowBadEvent X T q n) :
    dist (X (intervalClippedDyadicApprox T t n) ω) (X (intervalClippedDyadicApprox T s n) ω) ≤
      intervalDyadicStepThreshold q n := by
  let i := Nat.ceil ((s : ℝ) * (2 : ℝ) ^ n)
  let j := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  have hij_le : j ≤ i + 1 :=
    dyadicApproxIndices_adjacent_of_dist_le (s := s) (t := t) (n := n) hst hclose
  have hij_mono : i ≤ j := by
    have hscaled : (s : ℝ) * (2 : ℝ) ^ n ≤ (t : ℝ) * (2 : ℝ) ^ n := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hst) (by positivity)
    exact Nat.ceil_mono hscaled
  by_cases hij : i = j
  · have hsame : intervalClippedDyadicApprox T t n = intervalClippedDyadicApprox T s n := by
      simp [intervalClippedDyadicApprox, clippedRightDyadicApprox, rightDyadicApprox, i, j, hij]
    have hnonneg : 0 ≤ intervalDyadicStepThreshold q n := by
      unfold intervalDyadicStepThreshold
      positivity
    simpa [hsame] using hnonneg
  · have hj_eq : j = i + 1 := by
      omega
    have hj_le_cutoff : j ≤ dyadicCutoff T n := by
      simpa [j] using dyadicRightApprox_index_le_cutoff (t := t) (T := T) htT n
    have hi_lt_cutoff : i < dyadicCutoff T n := by
      omega
    have hrow :
        dist (X (dyadicPointUpTo T n (i + 1)) ω) (X (dyadicPointUpTo T n i) ω) ≤
          intervalDyadicStepThreshold q n :=
      dist_le_intervalDyadicStepThreshold_of_notMem_intervalDyadicRowBadEvent
        (X := X) (T := T) (q := q) (n := n) hgood hi_lt_cutoff
    -- Proof comment: when the row indices differ, they are consecutive, so the good-row bound
    -- applies to that adjacent pair directly.
    calc
      dist (X (intervalClippedDyadicApprox T t n) ω) (X (intervalClippedDyadicApprox T s n) ω)
          = dist (X (dyadicPointUpTo T n (i + 1)) ω) (X (dyadicPointUpTo T n i) ω) := by
              rw [show intervalClippedDyadicApprox T t n = dyadicPointUpTo T n (i + 1) by
                    simp [intervalClippedDyadicApprox, clippedRightDyadicApprox, rightDyadicApprox,
                      dyadicPointUpTo, i, j, hj_eq]]
              rw [show intervalClippedDyadicApprox T s n = dyadicPointUpTo T n i by
                    simp [intervalClippedDyadicApprox, clippedRightDyadicApprox, rightDyadicApprox,
                      dyadicPointUpTo, i]]
      _ ≤ intervalDyadicStepThreshold q n := hrow

/-- Helper for Exercise 21.1.1: if the refined dyadic row is good, two successive clipped
approximants of one fixed interval time differ by at most one good-row increment. -/
private lemma intervalClippedDyadicApprox_step_le_of_rowGood
    {X : ℝ≥0 → Ω → E} {T q : ℝ≥0} {t : ℝ≥0} {n : ℕ} {ω : Ω}
    (htT : t ≤ T)
    (hgood : ω ∉ intervalDyadicRowBadEvent X T q (n + 1)) :
    dist (X (intervalClippedDyadicApprox T t (n + 1)) ω) (X (intervalClippedDyadicApprox T t n) ω) ≤
      intervalDyadicStepThreshold q (n + 1) := by
  let j := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n)
  let j' := Nat.ceil ((t : ℝ) * (2 : ℝ) ^ (n + 1))
  have hcoarse :
      intervalClippedDyadicApprox T t n = dyadicPointUpTo T (n + 1) (2 * j) := by
    -- Proof comment: the coarse clipped approximant reappears on the refined row at the doubled
    -- coarse index.
    change dyadicPointUpTo T n j = dyadicPointUpTo T (n + 1) (2 * j)
    symm
    simpa [j] using dyadicPointUpTo_even T n j
  have hindices := refinedDyadicApproxIndices_adjacent t n
  dsimp [j, j'] at hindices
  rcases hindices with ⟨hj'le, htwice_le⟩
  by_cases hsame : j' = 2 * j
  · have hsamePoint :
        intervalClippedDyadicApprox T t (n + 1) = intervalClippedDyadicApprox T t n := by
      calc
        intervalClippedDyadicApprox T t (n + 1) = dyadicPointUpTo T (n + 1) j' := rfl
        _ = dyadicPointUpTo T (n + 1) (2 * j) := by rw [hsame]
        _ = intervalClippedDyadicApprox T t n := hcoarse.symm
    have hnonneg : 0 ≤ intervalDyadicStepThreshold q (n + 1) := by
      unfold intervalDyadicStepThreshold
      positivity
    simpa [hsamePoint] using hnonneg
  · have hadj : j' + 1 = 2 * j := by
      omega
    have hj_le : j ≤ dyadicCutoff T n := by
      exact dyadicRightApprox_index_le_cutoff (t := t) (T := T) htT n
    have h2j_le : 2 * j ≤ dyadicCutoff T (n + 1) := by
      calc
        2 * j ≤ 2 * dyadicCutoff T n := Nat.mul_le_mul_left 2 hj_le
        _ = dyadicCutoff T (n + 1) := by
          unfold dyadicCutoff
          simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    have hj'_lt : j' < dyadicCutoff T (n + 1) := by
      omega
    have hrow :
        dist (X (dyadicPointUpTo T (n + 1) (j' + 1)) ω) (X (dyadicPointUpTo T (n + 1) j') ω) ≤
          intervalDyadicStepThreshold q (n + 1) :=
      dist_le_intervalDyadicStepThreshold_of_notMem_intervalDyadicRowBadEvent
        (X := X) (T := T) (q := q) (n := n + 1) hgood hj'_lt
    -- Proof comment: in the adjacent-index case, the two clipped approximants are neighboring
    -- refined-row points.
    calc
      dist (X (intervalClippedDyadicApprox T t (n + 1)) ω) (X (intervalClippedDyadicApprox T t n) ω)
          = dist (X (dyadicPointUpTo T (n + 1) j') ω)
              (X (dyadicPointUpTo T (n + 1) (j' + 1)) ω) := by
                rw [show intervalClippedDyadicApprox T t (n + 1) = dyadicPointUpTo T (n + 1) j' by rfl,
                  hcoarse, hadj]
      _ = dist (X (dyadicPointUpTo T (n + 1) (j' + 1)) ω)
            (X (dyadicPointUpTo T (n + 1) j') ω) := by
              rw [dist_comm]
      _ ≤ intervalDyadicStepThreshold q (n + 1) := hrow

/-- Helper for Exercise 21.1.1: the adjacent-edge Markov estimate on an interval fiber. -/
private lemma measureReal_intervalDyadicAdjacentIncrement_gt_threshold_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → E} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    {n k : ℕ} (_hk : k < dyadicCutoff T n) :
    μ.real
      {ω | intervalDyadicStepThreshold q n <
        dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω)} ≤
      C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) /
        ((intervalDyadicStepThreshold q n) ^ (α : ℝ)) := by
  let s := dyadicPointUpTo T n k
  let t := dyadicPointUpTo T n (k + 1)
  let M : ℝ := C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ)))
  have hs : s ∈ Set.Icc (0 : ℝ≥0) T := by
    simpa [s] using dyadicPointUpTo_mem_Icc T n k
  have ht : t ∈ Set.Icc (0 : ℝ≥0) T := by
    simpa [t] using dyadicPointUpTo_mem_Icc T n (k + 1)
  have hαpos : 0 < (α : ℝ) := by
    exact_mod_cast h.alpha_pos
  have hβpow_pos : 0 < 1 + (β : ℝ) := by
    have hβpos : 0 < (β : ℝ) := by
      exact_mod_cast h.beta_pos
    linarith
  have hδpos : 0 < intervalDyadicStepThreshold q n := by
    unfold intervalDyadicStepThreshold
    positivity
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hmeas :
      AEMeasurable (fun ω ↦ edist (X t ω) (X s ω) ^ (α : ℝ)) μ := by
    -- Proof comment: fixed-time increment measurability is supplied by the canonical interval
    -- owner.
    exact
      ((h.isKolmogorovProcess.measurable_edist
        (s := ⟨t, ht⟩) (t := ⟨s, hs⟩)).aemeasurable).pow_const (α : ℝ)
  have hmesh :
      edist t s ^ (1 + (β : ℝ)) ≤
        ENNReal.ofReal ((((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ)))) := by
    have hdist : dist t s ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
      simpa [s, t, dist_comm] using dist_dyadicPointUpTo_succ_le_mesh T n k
    have hdist_enn :
        edist t s ≤ ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ n) := by
      simpa [edist_dist] using ENNReal.ofReal_le_ofReal hdist
    have hpow :
        edist t s ^ (1 + (β : ℝ)) ≤
          (ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ n)) ^ (1 + (β : ℝ)) :=
      ENNReal.rpow_le_rpow hdist_enn hβpow_pos.le
    calc
      edist t s ^ (1 + (β : ℝ))
          ≤ (ENNReal.ofReal ((1 : ℝ) / (2 : ℝ) ^ n)) ^ (1 + (β : ℝ)) := hpow
      _ = ENNReal.ofReal (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) := by
            rw [ENNReal.ofReal_rpow_of_nonneg
              (by positivity : 0 ≤ (1 : ℝ) / (2 : ℝ) ^ n) hβpow_pos.le]
  have hlintegral :
      ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤ ENNReal.ofReal M := by
    calc
      ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ
          ≤ (C : ℝ≥0∞) * edist t s ^ (1 + (β : ℝ)) := by
            simpa [s, t] using h.increment_lintegral_le (s := s) (t := t) hs.2 ht.2
      _ ≤ (C : ℝ≥0∞) *
            ENNReal.ofReal ((((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ)))) := by
              gcongr
      _ = ENNReal.ofReal M := by
            simp [M, ENNReal.ofReal_mul]
  -- Proof comment: the generic metric Markov bridge turns the interval moment estimate into the
  -- required real-valued tail bound.
  simpa [s, t, M, dist_comm] using
    measureReal_edist_gt_le_of_lintegral_bound
      (μ := μ)
      (Y := fun ω ↦ X t ω)
      (Z := fun ω ↦ X s ω)
      (hα := hαpos)
      (hδ := hδpos)
      (hM := hM_nonneg)
      hmeas
      hlintegral

/-- Helper for Exercise 21.1.1: the whole interval row bad event is controlled by summing the
adjacent-edge bounds over the finite row. -/
private lemma measureReal_intervalDyadicRowBadEvent_le_unionBound
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → E} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (n : ℕ) :
    μ.real (intervalDyadicRowBadEvent X T q n) ≤
      (Finset.range (dyadicCutoff T n)).sum (fun _ ↦
        C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) /
          ((intervalDyadicStepThreshold q n) ^ (α : ℝ))) := by
  let edgeEvent : ℕ → Set Ω := fun k ↦
    {ω | intervalDyadicStepThreshold q n <
      dist (X (dyadicPointUpTo T n (k + 1)) ω) (X (dyadicPointUpTo T n k) ω)}
  have hunion :
      intervalDyadicRowBadEvent X T q n = ⋃ k ∈ Finset.range (dyadicCutoff T n), edgeEvent k := by
    ext ω
    simp [intervalDyadicRowBadEvent, edgeEvent]
  -- Proof comment: the row-bad event is exactly the union of the finitely many adjacent-edge bad
  -- events.
  rw [hunion]
  calc
    μ.real (⋃ k ∈ Finset.range (dyadicCutoff T n), edgeEvent k)
        ≤ ∑ k ∈ Finset.range (dyadicCutoff T n), μ.real (edgeEvent k) :=
          MeasureTheory.measureReal_biUnion_finset_le (Finset.range (dyadicCutoff T n)) edgeEvent
    _ ≤ ∑ k ∈ Finset.range (dyadicCutoff T n),
          C * (((1 : ℝ) / (2 : ℝ) ^ n) ^ (1 + (β : ℝ))) /
            ((intervalDyadicStepThreshold q n) ^ (α : ℝ)) := by
          refine Finset.sum_le_sum ?_
          intro k hk_range
          exact measureReal_intervalDyadicAdjacentIncrement_gt_threshold_le
            (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q)
            h (_hk := Finset.mem_range.mp hk_range)

/-- Helper for Exercise 21.1.1: rewrite the interval row threshold as a genuine geometric
sequence in the row number. -/
private lemma intervalDyadicStepThreshold_eq_geomRatio_pow
    (q : ℝ≥0) (n : ℕ) :
    intervalDyadicStepThreshold q n = ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
  -- Proof comment: both sides are simply the expression `2^{-q n}` written in two convenient
  -- normal forms.
  calc
    intervalDyadicStepThreshold q n = (2 : ℝ) ^ (-((q : ℝ) * n)) := rfl
    _ = (2 : ℝ) ^ ((-(q : ℝ)) * n) := by congr 1; ring
    _ = ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
          rw [← Real.rpow_natCast, Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]

/-- Helper for Exercise 21.1.1: the interval row-bad probability has the expected geometric decay
when the admissible gap `β - α q` is positive. -/
private lemma measureReal_intervalDyadicRowBadEvent_le_geometric
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → E} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (_hgap : 0 < (β : ℝ) - (α : ℝ) * q)
    (n : ℕ) :
    μ.real (intervalDyadicRowBadEvent X T q n) ≤
      ((Nat.ceil (T : ℝ) : ℝ) * C) * ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n := by
  let mesh : ℝ := (1 : ℝ) / (2 : ℝ) ^ n
  let threshold : ℝ := intervalDyadicStepThreshold q n
  have hbase :
      μ.real (intervalDyadicRowBadEvent X T q n) ≤
        (dyadicCutoff T n : ℝ) *
          (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := by
    calc
      μ.real (intervalDyadicRowBadEvent X T q n)
          ≤ (Finset.range (dyadicCutoff T n)).sum (fun _ ↦
              C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := by
            simpa [mesh, threshold] using
              measureReal_intervalDyadicRowBadEvent_le_unionBound
                (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) h n
      _ = (dyadicCutoff T n : ℝ) *
            (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := by
            simp
  have hmesh_eq :
      mesh = (2 : ℝ) ^ (-(n : ℝ)) := by
    calc
      mesh = (1 / 2 : ℝ) ^ n := by
        dsimp [mesh]
        simp [one_div]
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        rw [Real.rpow_neg (by positivity : 0 ≤ (2 : ℝ))]
        rw [Real.rpow_natCast]
        simp [one_div]
  have hratio :
      C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ)) =
        C * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n := by
    have hthreshold_eq :
        threshold = (2 : ℝ) ^ (-((q : ℝ) * n)) := by
      rfl
    have hnum :
        mesh ^ (1 + (β : ℝ)) = (2 : ℝ) ^ ((-(n : ℝ)) * (1 + (β : ℝ))) := by
      rw [hmesh_eq, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    have hden :
        threshold ^ (α : ℝ) = (2 : ℝ) ^ ((-((q : ℝ) * n)) * (α : ℝ)) := by
      rw [hthreshold_eq, ← Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
    have hquot :
        mesh ^ (1 + (β : ℝ)) / (threshold ^ (α : ℝ)) =
          (2 : ℝ) ^ (((-(n : ℝ)) * (1 + (β : ℝ))) - ((-((q : ℝ) * n)) * (α : ℝ))) := by
      rw [hnum, hden, ← Real.rpow_sub zero_lt_two]
    calc
      C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))
          = C * (mesh ^ (1 + (β : ℝ)) / (threshold ^ (α : ℝ))) := by ring
      _ = C *
            (2 : ℝ) ^ (((-(n : ℝ)) * (1 + (β : ℝ))) - ((-((q : ℝ) * n)) * (α : ℝ))) := by
              rw [hquot]
      _ = C * (2 : ℝ) ^ (((α : ℝ) * q - (1 + (β : ℝ))) * n) := by
            congr 2
            ring
      _ = C * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n := by
            rw [← Real.rpow_natCast, Real.rpow_mul (by positivity : 0 ≤ (2 : ℝ))]
  have hcutoff :
      (dyadicCutoff T n : ℝ) = (Nat.ceil (T : ℝ) : ℝ) * (2 : ℝ) ^ n := by
    unfold dyadicCutoff
    simp [Nat.cast_mul, Nat.cast_pow]
  have hfinal :
      (dyadicCutoff T n : ℝ) *
          (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) =
        ((Nat.ceil (T : ℝ) : ℝ) * C) * ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n := by
    rw [hcutoff, hratio]
    calc
      ((Nat.ceil (T : ℝ) : ℝ) * (2 : ℝ) ^ n) *
          (C * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n)
          = ((Nat.ceil (T : ℝ) : ℝ) * C) *
              ((2 : ℝ) ^ n * ((2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n) := by
                ring
      _ = ((Nat.ceil (T : ℝ) : ℝ) * C) *
            ((((2 : ℝ) ^ (1 : ℝ)) *
                (2 : ℝ) ^ ((α : ℝ) * q - (1 + (β : ℝ)))) ^ n) := by
              rw [show (2 : ℝ) ^ n = ((2 : ℝ) ^ (1 : ℝ)) ^ n by simp, ← mul_pow]
      _ = ((Nat.ceil (T : ℝ) : ℝ) * C) *
            (((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n) := by
              congr 2
              rw [← Real.rpow_add zero_lt_two]
              congr 1
              ring
  -- Proof comment: after the finite union bound, the remaining arithmetic collapses to one
  -- geometric factor in the row number.
  calc
    μ.real (intervalDyadicRowBadEvent X T q n)
        ≤ (dyadicCutoff T n : ℝ) *
            (C * (mesh ^ (1 + (β : ℝ))) / (threshold ^ (α : ℝ))) := hbase
    _ = ((Nat.ceil (T : ℝ) : ℝ) * C) * ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n := hfinal

/-- Helper for Exercise 21.1.1: the interval row-bad masses are summable as soon as
`q < β / α`. -/
private lemma summable_measureReal_intervalDyadicRowBadEvent
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℝ≥0 → Ω → E} {T α β C q : ℝ≥0}
    (h : IsKolmogorovProcessOnIcc μ X T α β C)
    (hq : (q : ℝ) < β / α) :
    Summable (fun n : ℕ => μ.real (intervalDyadicRowBadEvent X T q n)) := by
  have hαpos : 0 < (α : ℝ) := by
    exact_mod_cast h.alpha_pos
  have hgap : 0 < (β : ℝ) - (α : ℝ) * q := by
    have hmul_lt : (q : ℝ) * α < β := by
      exact (lt_div_iff₀ hαpos).mp hq
    nlinarith [hmul_lt]
  let ρ : ℝ := (2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_one : ρ < 1 := by
    dsimp [ρ]
    have hexp_neg : ((α : ℝ) * q - (β : ℝ)) < 0 := by
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) hexp_neg
  have hgeom :
      Summable (fun n : ℕ ↦ ((Nat.ceil (T : ℝ) : ℝ) * C) * ρ ^ n) :=
    (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left ((Nat.ceil (T : ℝ) : ℝ) * C)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro n
    exact MeasureTheory.measureReal_nonneg
  · intro n
    simpa [ρ] using
      measureReal_intervalDyadicRowBadEvent_le_geometric
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q) h hgap n

/-- Helper for Exercise 21.1.1: one coordinate-fiber bad-row event is the interval bad-row event
for the corresponding translated fiber process. -/
private def cubeDyadicFiberBadEvent
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T q : ℝ≥0) (n : ℕ) (i : Fin d) (a : cubeFiberAnchor (d := d) T n i) : Set Ω :=
  intervalDyadicRowBadEvent
    (fun u ω ↦ X (cubeFiberPoint (d := d) T n i a u).1 ω)
    (2 * T)
    q
    n

/-- Helper for Exercise 21.1.1: the cube row-bad event is the finite union of all bad coordinate
fibers at the fixed dyadic level `n`. -/
private def cubeDyadicRowBadEvent
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T q : ℝ≥0) (n : ℕ) : Set Ω :=
  ⋃ i : Fin d, ⋃ a : cubeFiberAnchor (d := d) T n i,
    cubeDyadicFiberBadEvent (d := d) X T q n i a

/-- Helper for Exercise 21.1.1: the repaired boundary-inclusive anchor family on one fiber has
cardinality `(dyadicCutoff (2 * T) n + 1)^(d - 1)`. -/
private lemma cubeFiberAnchor_card
    (T : ℝ≥0) (n : ℕ) (i : Fin d) :
    Fintype.card (cubeFiberAnchor (d := d) T n i) = (dyadicCutoff (2 * T) n + 1) ^ (d - 1) := by
  have hdomain : Fintype.card {j : Fin d // j ≠ i} = d - 1 := by
    rw [Fintype.card_of_subtype {j : Fin d | j ≠ i}]
    · rw [Finset.filter_not, Finset.filter_eq' _ i, if_pos (Finset.mem_univ _),
        Finset.card_sdiff, Finset.card_univ]
      simp
    · simp
  -- Proof comment: once the excluded coordinate set has size `d - 1`, the anchors are just
  -- functions from that finite set into the row index set.
  dsimp [cubeFiberAnchor]
  rw [Fintype.card_fun, hdomain, Fintype.card_fin]

/-- Helper for Exercise 21.1.1: after adding the terminal anchor, the number of frozen coordinate
choices is still bounded by an `n`-independent horizon factor times the mesh factor. -/
private lemma cubeFiberAnchor_count_le_geometric
    (T : ℝ≥0) (n : ℕ) :
    (((dyadicCutoff (2 * T) n + 1 : ℕ) : ℝ) ^ (d - 1)) ≤
      (((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) ^ (d - 1)) * ((2 : ℝ) ^ n) ^ (d - 1) := by
  let A : ℝ := (Nat.ceil ((2 : ℝ) * T) : ℝ) + 1
  have hone_pow_nat : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (Nat.two_pow_pos n)
  have hone_pow : (1 : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast hone_pow_nat
  have hbase :
      ((dyadicCutoff (2 * T) n + 1 : ℕ) : ℝ) ≤ A * (2 : ℝ) ^ n := by
    calc
      ((dyadicCutoff (2 * T) n + 1 : ℕ) : ℝ)
          = (dyadicCutoff (2 * T) n : ℝ) + 1 := by
              norm_num
      _ = (Nat.ceil ((2 : ℝ) * T) : ℝ) * (2 : ℝ) ^ n + 1 := by
            simp [dyadicCutoff, Nat.cast_mul, Nat.cast_pow]
      _ ≤ (Nat.ceil ((2 : ℝ) * T) : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ n := by
            gcongr
      _ = A * (2 : ℝ) ^ n := by
            dsimp [A]
            ring
  have hpow :
      (((dyadicCutoff (2 * T) n + 1 : ℕ) : ℝ) ^ (d - 1)) ≤
        (A * (2 : ℝ) ^ n) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) hbase (d - 1)
  simpa [A, mul_pow] using hpow

/-- Helper for Exercise 21.1.1: the cube row-bad event is bounded by summing the interval
fiber-event estimates over all coordinates and all anchors. -/
private lemma measureReal_cubeDyadicRowBadEvent_le_fiberSum
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T α β C q : ℝ≥0}
    (hβ : 0 < β)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (hgap : 0 < (β : ℝ) - (α : ℝ) * q)
    (n : ℕ) :
    μ.real (cubeDyadicRowBadEvent (d := d) X T q n) ≤
      ∑ i : Fin d, ∑ _a : cubeFiberAnchor (d := d) T n i,
        ((((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) * C) *
          ((2 : ℝ) ^
            ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))) ^ n) := by
  have hfiberGap :
      0 < ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)) - (α : ℝ) * q := by
    have hnonneg : 0 ≤ (((d - 1 : ℕ) : ℝ≥0) : ℝ) := by positivity
    linarith
  have hrewrite :
      cubeDyadicRowBadEvent (d := d) X T q n =
        ⋃ i ∈ (Finset.univ : Finset (Fin d)),
          ⋃ a ∈ (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i)),
            cubeDyadicFiberBadEvent (d := d) X T q n i a := by
    ext ω
    simp [cubeDyadicRowBadEvent, cubeDyadicFiberBadEvent]
  rw [hrewrite]
  calc
    μ.real
        (⋃ i ∈ (Finset.univ : Finset (Fin d)),
          ⋃ a ∈ (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i)),
            cubeDyadicFiberBadEvent (d := d) X T q n i a)
        ≤
          ∑ i ∈ (Finset.univ : Finset (Fin d)),
            μ.real
              (⋃ a ∈ (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i)),
                cubeDyadicFiberBadEvent (d := d) X T q n i a) := by
          exact
            MeasureTheory.measureReal_biUnion_finset_le
              (μ := μ)
              (Finset.univ : Finset (Fin d))
              (fun i ↦
                ⋃ a ∈ (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i)),
                  cubeDyadicFiberBadEvent (d := d) X T q n i a)
    _ ≤
        ∑ i ∈ (Finset.univ : Finset (Fin d)),
          ∑ a ∈ (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i)),
            μ.real (cubeDyadicFiberBadEvent (d := d) X T q n i a) := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact
            MeasureTheory.measureReal_biUnion_finset_le
              (μ := μ)
              (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i))
              (fun a ↦ cubeDyadicFiberBadEvent (d := d) X T q n i a)
    _ ≤
        ∑ i ∈ (Finset.univ : Finset (Fin d)),
          ∑ _a ∈ (Finset.univ : Finset (cubeFiberAnchor (d := d) T n i)),
            ((((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) * C) *
              ((2 : ℝ) ^
                ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))) ^ n) := by
          refine Finset.sum_le_sum ?_
          intro i _
          refine Finset.sum_le_sum ?_
          intro a _
          have hfiber :
              IsKolmogorovProcessOnIcc μ
                (fun u ω ↦ X (cubeFiberPoint (d := d) T n i a u).1 ω)
                (2 * T) α (((d - 1 : ℕ) : ℝ≥0) + β) C :=
            cubeFiberProcess_isKolmogorovProcessOnIcc
              (μ := μ) (X := X) (α := α) (β := β) (T := T) (C := C)
              hβ hC n i a
          -- Proof comment: each fiber is a genuine one-dimensional Kolmogorov process, so the
          -- interval geometric estimate applies with exponent parameter `(d - 1) + β`.
          have hfiberMeasure :
              μ.real (cubeDyadicFiberBadEvent (d := d) X T q n i a) ≤
                (((Nat.ceil ((2 : ℝ) * T) : ℝ) * C) *
                  ((2 : ℝ) ^
                    ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))) ^ n) := by
            simpa [cubeDyadicFiberBadEvent] using
              measureReal_intervalDyadicRowBadEvent_le_geometric
                (μ := μ)
                (X := fun u ω ↦ X (cubeFiberPoint (d := d) T n i a u).1 ω)
                (T := 2 * T)
                (α := α)
                (β := (((d - 1 : ℕ) : ℝ≥0) + β))
                (C := C)
                (q := q)
                hfiber
                hfiberGap
                n
          have hconst :
              ((Nat.ceil ((2 : ℝ) * T) : ℝ) * C) ≤
                (((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) * C) := by
            nlinarith [show (0 : ℝ) ≤ C by positivity]
          calc
            μ.real (cubeDyadicFiberBadEvent (d := d) X T q n i a) ≤
                (((Nat.ceil ((2 : ℝ) * T) : ℝ) * C) *
                  ((2 : ℝ) ^
                    ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))) ^ n) :=
              hfiberMeasure
            _ ≤
                ((((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) * C) *
                  ((2 : ℝ) ^
                    ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))) ^ n) := by
                  gcongr
    _ = ∑ i : Fin d, ∑ _a : cubeFiberAnchor (d := d) T n i,
          ((((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) * C) *
            ((2 : ℝ) ^
              ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))) ^ n) := by
          simp

/-- Helper for Exercise 21.1.1: after counting the finite family of coordinate fibers, the cube
row-bad masses still satisfy a geometric decay in the dyadic level. -/
private lemma measureReal_cubeDyadicRowBadEvent_le_geometric
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T α β C q : ℝ≥0}
    (hβ : 0 < β)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (hgap : 0 < (β : ℝ) - (α : ℝ) * q)
    (n : ℕ) :
    μ.real (cubeDyadicRowBadEvent (d := d) X T q n) ≤
      (((d : ℝ) * ((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) ^ d * C) *
        ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n) := by
  by_cases hd0 : d = 0
  · subst hd0
    -- Proof comment: in dimension `0` there are no coordinate fibers, so the cube bad event is
    -- empty and the geometric bound is trivial.
    simp [cubeDyadicRowBadEvent]
  · let A : ℝ := (Nat.ceil ((2 : ℝ) * T) : ℝ) + 1
    let ρ₀ : ℝ := (2 : ℝ) ^ ((α : ℝ) * q - ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)))
    let ρ : ℝ := (2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd0
    have hbase :=
      measureReal_cubeDyadicRowBadEvent_le_fiberSum
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q)
        hβ hC hgap n
    have hcount :
        ∑ i : Fin d, ∑ _a : cubeFiberAnchor (d := d) T n i, (A * C) * ρ₀ ^ n =
          (d : ℝ) * (((dyadicCutoff (2 * T) n + 1 : ℕ) : ℝ) ^ (d - 1)) * ((A * C) * ρ₀ ^ n) := by
      -- Proof comment: every coordinate contributes the same number of anchors, so the double sum
      -- collapses to the product of the number of coordinates, the number of anchors, and one
      -- fiber contribution.
      simp [A, mul_assoc, mul_left_comm, mul_comm]
    have hA_pow : A ^ (d - 1) * A = A ^ d := by
      rw [mul_comm, ← pow_succ']
      congr
      omega
    have htwo_pow :
        ((2 : ℝ) ^ n) ^ (d - 1) = ((2 : ℝ) ^ (d - 1)) ^ n := by
      calc
        ((2 : ℝ) ^ n) ^ (d - 1) = (2 : ℝ) ^ (n * (d - 1)) := by
          rw [pow_mul]
        _ = (2 : ℝ) ^ ((d - 1) * n) := by rw [Nat.mul_comm]
        _ = ((2 : ℝ) ^ (d - 1)) ^ n := by
          rw [pow_mul]
    have hρ_merge :
        ((2 : ℝ) ^ n) ^ (d - 1) * ρ₀ ^ n = ρ ^ n := by
      rw [htwo_pow, ← mul_pow]
      have hρ_base : (2 : ℝ) ^ (d - 1) * ρ₀ = ρ := by
        dsimp [ρ, ρ₀]
        have hcast :
            ((((d - 1 : ℕ) : ℝ≥0) + β : ℝ)) =
              ((d - 1 : ℕ) : ℝ) + β := by
          rfl
        rw [show (2 : ℝ) ^ (d - 1) = (2 : ℝ) ^ ((d - 1 : ℕ) : ℝ) by
              rw [Real.rpow_natCast]]
        rw [← Real.rpow_add zero_lt_two]
        rw [hcast]
        congr 1
        ring
      rw [hρ_base]
    calc
      μ.real (cubeDyadicRowBadEvent (d := d) X T q n) ≤
          ∑ i : Fin d, ∑ _a : cubeFiberAnchor (d := d) T n i, (A * C) * ρ₀ ^ n := by
            simpa [A, ρ₀] using hbase
      _ = (d : ℝ) * (((dyadicCutoff (2 * T) n + 1 : ℕ) : ℝ) ^ (d - 1)) * ((A * C) * ρ₀ ^ n) :=
            hcount
      _ ≤ (d : ℝ) * (A ^ (d - 1) * ((2 : ℝ) ^ n) ^ (d - 1)) * ((A * C) * ρ₀ ^ n) := by
            gcongr
            exact cubeFiberAnchor_count_le_geometric (d := d) T n
      _ = (d : ℝ) * (A ^ (d - 1) * A) * C * (((2 : ℝ) ^ n) ^ (d - 1) * ρ₀ ^ n) := by
            ring
      _ = (d : ℝ) * A ^ d * C * ρ ^ n := by
            rw [hA_pow, hρ_merge]
      _ = (((d : ℝ) * A ^ d * C) * ρ ^ n) := by ring
      _ = (((d : ℝ) * ((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) ^ d * C) *
            ((2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))) ^ n) := by
            simp [A, ρ]

/-- Helper for Exercise 21.1.1: the cube row-bad masses are summable whenever `q < β / α`. -/
private lemma summable_measureReal_cubeDyadicRowBadEvent
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T α β C q : ℝ≥0}
    (hβ : 0 < β)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (hq : (q : ℝ) < β / α) :
    Summable (fun n : ℕ ↦ μ.real (cubeDyadicRowBadEvent (d := d) X T q n)) := by
  have hαpos : 0 < (α : ℝ) := hC.p_pos
  have hgap : 0 < (β : ℝ) - (α : ℝ) * q := by
    have hmul_lt : (q : ℝ) * α < β := by
      exact (lt_div_iff₀ hαpos).mp hq
    nlinarith
  let ρ : ℝ := (2 : ℝ) ^ ((α : ℝ) * q - (β : ℝ))
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    positivity
  have hρ_lt_one : ρ < 1 := by
    dsimp [ρ]
    have hexp_neg : ((α : ℝ) * q - (β : ℝ)) < 0 := by
      linarith
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) hexp_neg
  have hgeom :
      Summable
        (fun n : ℕ ↦
          (((d : ℝ) * ((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) ^ d * C) * ρ ^ n)) :=
    (summable_geometric_of_lt_one hρ_nonneg hρ_lt_one).mul_left
      (((d : ℝ) * ((Nat.ceil ((2 : ℝ) * T) : ℝ) + 1) ^ d * C))
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro n
    exact MeasureTheory.measureReal_nonneg
  · intro n
    simpa [ρ] using
      measureReal_cubeDyadicRowBadEvent_le_geometric
        (μ := μ) (X := X) (T := T) (α := α) (β := β) (C := C) (q := q)
        hβ hC hgap n

/-- Helper for Exercise 21.1.1: choose a concrete cube row after which all later dyadic rows are
good along one sample path. -/
private noncomputable def eventualCubeGoodRowStart
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T q : ℝ≥0} {ω : Ω}
    (hgood : ∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) : ℕ :=
  Classical.choose (Filter.eventually_atTop.mp hgood)

/-- Helper for Exercise 21.1.1: every cube row at or beyond the chosen index is good. -/
private lemma eventualCubeGoodRowStart_spec
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T q : ℝ≥0} {ω : Ω}
    (hgood : ∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    ∀ n ≥ eventualCubeGoodRowStart (d := d) (X := X) (T := T) (q := q) hgood,
      ω ∉ cubeDyadicRowBadEvent (d := d) X T q n :=
  Classical.choose_spec (Filter.eventually_atTop.mp hgood)

/-- Helper for Exercise 21.1.1: one cube coordinate is approximated by translating it into
`[0, 2T]`, applying the interval dyadic approximation there, and translating back by `-T`. -/
private noncomputable def cubeClippedDyadicApproxCoordinate
    (T : ℝ≥0) (x : ℝ) (n : ℕ) : ℝ :=
  ((clippedRightDyadicApprox (2 * T) (Real.toNNReal (x + T)) n : ℝ≥0) : ℝ) - T

/-- Helper for Exercise 21.1.1: the translated dyadic coordinate uses the right-dyadic ceil index
of the shifted coordinate `x + T`. -/
private noncomputable def cubeDyadicApproxIndex
    (T : ℝ≥0) (x : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (((Real.toNNReal (x + T) : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)

/-- Helper for Exercise 21.1.1: on cube coordinates, the translated dyadic approximation is the
shifted interval dyadic point at the corresponding ceil index. -/
private lemma cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
    {T : ℝ≥0} {x : ℝ}
    (hx : x ∈ Set.Icc (-(T : ℝ)) (T : ℝ)) (n : ℕ) :
    cubeClippedDyadicApproxCoordinate T x n =
      ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T x n) : NNReal) : ℝ) - T := by
  have hx_nonneg : 0 ≤ x + T := by
    linarith [hx.1]
  -- Proof comment: once `x + T` is recognized as nonnegative, both definitions are the same
  -- clipped right-dyadic approximation written with different owner names.
  simp [cubeClippedDyadicApproxCoordinate, cubeDyadicApproxIndex, dyadicPointUpTo,
    clippedRightDyadicApprox, rightDyadicApprox, Real.toNNReal_of_nonneg hx_nonneg]

/-- Helper for Exercise 21.1.1: the translated coordinatewise dyadic approximation stays inside
the cube interval `[-T, T]`. -/
private lemma cubeClippedDyadicApproxCoordinate_mem_Icc
    {T : ℝ≥0} {x : ℝ} (n : ℕ) :
    cubeClippedDyadicApproxCoordinate T x n ∈ Set.Icc (-(T : ℝ)) (T : ℝ) := by
  have hclip :
      clippedRightDyadicApprox (2 * T) (Real.toNNReal (x + T)) n ∈
        Set.Icc (0 : ℝ≥0) (2 * T) :=
    clippedRightDyadicApprox_mem_Icc (2 * T) (Real.toNNReal (x + T)) n
  have hclip_nonneg :
      (0 : ℝ) ≤ (clippedRightDyadicApprox (2 * T) (Real.toNNReal (x + T)) n : ℝ) := by
    exact_mod_cast hclip.1
  have hclip_le :
      (clippedRightDyadicApprox (2 * T) (Real.toNNReal (x + T)) n : ℝ) ≤
        (2 : ℝ) * T := by
    exact_mod_cast hclip.2
  constructor
  · dsimp [cubeClippedDyadicApproxCoordinate]
    linarith
  · dsimp [cubeClippedDyadicApproxCoordinate]
    linarith

/-- Helper for Exercise 21.1.1: the translated coordinatewise dyadic approximation converges back
to the original cube coordinate. -/
private lemma tendsto_cubeClippedDyadicApproxCoordinate
    {T : ℝ≥0} {x : ℝ}
    (hx : x ∈ Set.Icc (-(T : ℝ)) (T : ℝ)) :
    Filter.Tendsto (cubeClippedDyadicApproxCoordinate T x) Filter.atTop (nhds x) := by
  have hx_nonneg : 0 ≤ x + T := by
    linarith [hx.1]
  have hx_le : Real.toNNReal (x + T) ≤ 2 * T := by
    rw [Real.toNNReal_of_nonneg hx_nonneg]
    have hx_le' : x + T ≤ (2 : ℝ) * T := by
      linarith [hx.2]
    exact hx_le'
  have hbase :
      Filter.Tendsto
        (fun n ↦ ((clippedRightDyadicApprox (2 * T) (Real.toNNReal (x + T)) n : ℝ≥0) : ℝ))
        Filter.atTop
        (nhds (x + T)) := by
    -- Proof comment: first use the clipped dyadic ceiling approximation theorem on `[0, 2T]`,
    -- then coerce the limit from `NNReal` back to `ℝ`.
    simpa [Real.toNNReal_of_nonneg hx_nonneg] using
      (continuous_subtype_val.continuousAt.tendsto.comp
        (tendsto_clippedRightDyadicApprox hx_le))
  -- Proof comment: subtracting the fixed translation parameter `T` recovers the original cube
  -- coordinate.
  have hshift :
      Filter.Tendsto
        (fun n ↦ ((clippedRightDyadicApprox (2 * T) (Real.toNNReal (x + T)) n : ℝ≥0) : ℝ) - T)
        Filter.atTop
        (nhds ((x + T) - T)) := by
    exact hbase.sub
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ ↦ (T : ℝ)) Filter.atTop (nhds (T : ℝ)))
  simpa [cubeClippedDyadicApproxCoordinate] using hshift

/-- Helper for Exercise 21.1.1: the theorem-local cube dyadic approximation is obtained by
applying the translated one-dimensional approximation to every coordinate. -/
private noncomputable def cubeClippedDyadicApprox
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) :
    euclideanClosedCube d (T : ℝ) :=
  ⟨WithLp.toLp 2 (fun i : Fin d ↦ cubeClippedDyadicApproxCoordinate T (t.1 i) n), by
    intro i
    exact cubeClippedDyadicApproxCoordinate_mem_Icc (T := T) (x := t.1 i) n⟩

/-- Helper for Exercise 21.1.1: the cube dyadic approximation has the expected coordinate
formula. -/
private lemma cubeClippedDyadicApprox_apply
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) (i : Fin d) :
    (cubeClippedDyadicApprox (d := d) T t n : EuclideanSpace ℝ (Fin d)) i =
      cubeClippedDyadicApproxCoordinate T (t.1 i) n := by
  simp [cubeClippedDyadicApprox]

/-- Helper for Exercise 21.1.1: every cube dyadic-approximant coordinate is a shifted interval
dyadic point at the translated ceil index. -/
private lemma cubeClippedDyadicApprox_apply_eq_dyadicPointUpTo_sub
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) (i : Fin d) :
    (cubeClippedDyadicApprox (d := d) T t n : EuclideanSpace ℝ (Fin d)) i =
      ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (t.1 i) n) : NNReal) : ℝ) - T := by
  -- Proof comment: this is the coordinate normal form used later to match dyadic approximants to
  -- repaired coordinate fibers.
  rw [cubeClippedDyadicApprox_apply]
  exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub (T := T) (x := t.1 i) (t.2 i) n

/-- Helper for Exercise 21.1.1: the row-step chain replaces the first `m` coordinates of the row
`n` approximant by the row `n + 1` values and leaves the remaining coordinates unchanged. -/
private noncomputable def cubeStepChainPoint
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) :
    euclideanClosedCube d (T : ℝ) :=
  ⟨WithLp.toLp 2 fun i : Fin d =>
      if i.1 < m then
        cubeClippedDyadicApproxCoordinate T (t.1 i) (n + 1)
      else
        cubeClippedDyadicApproxCoordinate T (t.1 i) n, by
    intro i
    by_cases hi : i.1 < m
    · -- Proof comment: replaced coordinates still lie in the cube because each translated
      -- one-dimensional approximant does.
      simpa [hi] using
        cubeClippedDyadicApproxCoordinate_mem_Icc (T := T) (x := t.1 i) (n := n + 1)
    · -- Proof comment: untouched coordinates keep their row-`n` dyadic value, which stays in the
      -- same interval.
      simpa [hi] using
        cubeClippedDyadicApproxCoordinate_mem_Icc (T := T) (x := t.1 i) (n := n)⟩

/-- Helper for Exercise 21.1.1: the coordinate formula for the row-step chain is just the defining
piecewise replacement. -/
private lemma cubeStepChainPoint_apply
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (i : Fin d) :
    (cubeStepChainPoint (d := d) T t n m : EuclideanSpace ℝ (Fin d)) i =
      if i.1 < m then
        cubeClippedDyadicApproxCoordinate T (t.1 i) (n + 1)
      else
        cubeClippedDyadicApproxCoordinate T (t.1 i) n := by
  simp [cubeStepChainPoint]

/-- Helper for Exercise 21.1.1: the row-step chain starts at the row-`n` dyadic approximant. -/
private lemma cubeStepChainPoint_zero
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) :
    cubeStepChainPoint (d := d) T t n 0 = cubeClippedDyadicApprox (d := d) T t n := by
  ext i
  -- Proof comment: with `m = 0`, no coordinate has been replaced yet.
  simp [cubeStepChainPoint_apply, cubeClippedDyadicApprox_apply]

/-- Helper for Exercise 21.1.1: after replacing all `d` coordinates, the row-step chain lands on
the row `n + 1` dyadic approximant. -/
private lemma cubeStepChainPoint_all
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) :
    cubeStepChainPoint (d := d) T t n d = cubeClippedDyadicApprox (d := d) T t (n + 1) := by
  ext i
  -- Proof comment: every `Fin d` index satisfies `i.1 < d`, so all coordinates have been
  -- replaced by the refined row values.
  have hi : i.1 < d := i.2
  simp [cubeStepChainPoint_apply, cubeClippedDyadicApprox_apply, hi]

/-- Helper for Exercise 21.1.1: each translated cube dyadic index stays below the dyadic cutoff
for the shifted interval `[0, 2T]`. -/
private lemma cubeDyadicApproxIndex_le_cutoff
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) (i : Fin d) :
    cubeDyadicApproxIndex T (t.1 i) n ≤ dyadicCutoff (2 * T) n := by
  have hi := t.2 i
  have hnonneg : 0 ≤ t.1 i + T := by
    linarith [hi.1]
  have hle : Real.toNNReal (t.1 i + T) ≤ 2 * T := by
    rw [Real.toNNReal_of_nonneg hnonneg]
    change t.1 i + T ≤ (2 : ℝ) * T
    linarith [hi.2]
  -- Proof comment: translating a cube coordinate by `+T` moves it into `[0, 2T]`, where the
  -- standard interval cutoff estimate applies unchanged.
  simpa [cubeDyadicApproxIndex, Real.toNNReal_of_nonneg hnonneg] using
    dyadicRightApprox_index_le_cutoff
      (t := Real.toNNReal (t.1 i + T))
      (T := 2 * T)
      hle
      n

/-- Helper for Exercise 21.1.1: doubling a coarse translated cube dyadic index lands in the next
refined cutoff row. -/
private lemma two_mul_cubeDyadicApproxIndex_le_refinedCutoff
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) (i : Fin d) :
    2 * cubeDyadicApproxIndex T (t.1 i) n ≤ dyadicCutoff (2 * T) (n + 1) := by
  calc
    2 * cubeDyadicApproxIndex T (t.1 i) n ≤ 2 * dyadicCutoff (2 * T) n := by
      exact Nat.mul_le_mul_left 2 (cubeDyadicApproxIndex_le_cutoff (d := d) T t n i)
    _ = dyadicCutoff (2 * T) (n + 1) := by
      unfold dyadicCutoff
      simp [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]

/-- Helper for Exercise 21.1.1: the `m`-th row-step chain comparison is controlled by one
refined-row coordinate fiber whose earlier coordinates are already refined and whose later
coordinates are the doubled coarse anchors. -/
private noncomputable def cubeStepChainAnchor
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) :
    cubeFiberAnchor (d := d) T (n + 1) ⟨m, hm⟩ :=
  fun j =>
    if hj : j.1.1 < m then
      ⟨cubeDyadicApproxIndex T (t.1 j.1) (n + 1), by
        exact lt_of_le_of_lt
          (cubeDyadicApproxIndex_le_cutoff (d := d) T t (n + 1) j.1)
          (Nat.lt_succ_self _)⟩
    else
      ⟨2 * cubeDyadicApproxIndex T (t.1 j.1) n, by
        exact lt_of_le_of_lt
          (two_mul_cubeDyadicApproxIndex_le_refinedCutoff (d := d) T t n j.1)
          (Nat.lt_succ_self _)⟩

/-- Helper for Exercise 21.1.1: the `m`-th row-step chain point is the corresponding refined-row
fiber point evaluated at the coarse translated dyadic time of the varying coordinate. -/
private lemma cubeStepChainPoint_eq_cubeFiberPoint_coarse
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) :
    cubeStepChainPoint (d := d) T t n m =
      cubeFiberPoint
        (d := d)
        T
        (n + 1)
        ⟨m, hm⟩
        (cubeStepChainAnchor (d := d) T t n m hm)
        (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 ⟨m, hm⟩ + T)) n) := by
  ext k
  let i : Fin d := ⟨m, hm⟩
  by_cases hk : k = i
  · subst hk
    -- Proof comment: on the varying coordinate, both sides are the same translated coarse dyadic
    -- approximation of `t`.
    simp [i, cubeStepChainPoint_apply, cubeFiberPoint_apply_same, cubeClippedDyadicApproxCoordinate,
      intervalClippedDyadicApprox, clippedRightDyadicApprox]
  · have hk' : k ≠ i := hk
    by_cases hlt : k.1 < m
    · -- Proof comment: earlier coordinates were already refined, so the fiber anchor stores the
      -- refined row-`n + 1` dyadic value directly.
      calc
        (cubeStepChainPoint (d := d) T t n m : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (t.1 k) (n + 1) := by
                simp [cubeStepChainPoint_apply, hlt]
        _ = ((dyadicPointUpTo (2 * T) (n + 1) (cubeDyadicApproxIndex T (t.1 k) (n + 1)) :
              NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := t.1 k) (t.2 k) (n + 1)
        _ = (cubeFiberPoint
              (d := d)
              T
              (n + 1)
              i
              (cubeStepChainAnchor (d := d) T t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n + 1) (i := i) (j := k)
                (a := cubeStepChainAnchor (d := d) T t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n) hk']
              simp [cubeStepChainAnchor, i, hlt]
    · -- Proof comment: later coordinates still sit at the coarse row, which the refined row sees
      -- again at the doubled coarse index.
      calc
        (cubeStepChainPoint (d := d) T t n m : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (t.1 k) n := by
                simp [cubeStepChainPoint_apply, hlt]
        _ = ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (t.1 k) n) : NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := t.1 k) (t.2 k) n
        _ = ((dyadicPointUpTo (2 * T) (n + 1) (2 * cubeDyadicApproxIndex T (t.1 k) n) :
              NNReal) : ℝ) - T := by
              rw [dyadicPointUpTo_even]
        _ = (cubeFiberPoint
              (d := d)
              T
              (n + 1)
              i
              (cubeStepChainAnchor (d := d) T t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n + 1) (i := i) (j := k)
                (a := cubeStepChainAnchor (d := d) T t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n) hk']
              simp [cubeStepChainAnchor, i, hlt]

/-- Helper for Exercise 21.1.1: the next row-step chain point is the same refined-row fiber
point evaluated at the refined translated dyadic time of the varying coordinate. -/
private lemma cubeStepChainPoint_eq_cubeFiberPoint_refined
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) :
    cubeStepChainPoint (d := d) T t n (m + 1) =
      cubeFiberPoint
        (d := d)
        T
        (n + 1)
        ⟨m, hm⟩
        (cubeStepChainAnchor (d := d) T t n m hm)
        (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 ⟨m, hm⟩ + T)) (n + 1)) := by
  ext k
  let i : Fin d := ⟨m, hm⟩
  by_cases hk : k = i
  · subst hk
    -- Proof comment: on the varying coordinate, the successor chain point already uses the
    -- refined row value, which is exactly the refined fiber evaluation.
    simp [i, cubeStepChainPoint_apply, cubeFiberPoint_apply_same, cubeClippedDyadicApproxCoordinate,
      intervalClippedDyadicApprox, clippedRightDyadicApprox]
  · have hk' : k ≠ i := hk
    have hk_ne_val : k.1 ≠ m := by
      intro hkval
      apply hk
      exact Fin.ext hkval
    by_cases hlt : k.1 < m
    · -- Proof comment: coordinates strictly before `m` already use refined row values on both
      -- sides of the identification.
      calc
        (cubeStepChainPoint (d := d) T t n (m + 1) : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (t.1 k) (n + 1) := by
                have hklt : k.1 < m + 1 := by omega
                simp [cubeStepChainPoint_apply, hklt]
        _ = ((dyadicPointUpTo (2 * T) (n + 1) (cubeDyadicApproxIndex T (t.1 k) (n + 1)) :
              NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := t.1 k) (t.2 k) (n + 1)
        _ = (cubeFiberPoint
              (d := d)
              T
              (n + 1)
              i
              (cubeStepChainAnchor (d := d) T t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) (n + 1)) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n + 1) (i := i) (j := k)
                (a := cubeStepChainAnchor (d := d) T t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) (n + 1))
                hk']
              simp [cubeStepChainAnchor, i, hlt]
    · -- Proof comment: coordinates strictly after `m` still use the coarse row, so the same
      -- doubled-index rewrite as above identifies them with the refined-row fiber anchor.
      calc
        (cubeStepChainPoint (d := d) T t n (m + 1) : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (t.1 k) n := by
                have hnot : ¬ k.1 < m + 1 := by
                  omega
                simp [cubeStepChainPoint_apply, hnot]
        _ = ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (t.1 k) n) : NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := t.1 k) (t.2 k) n
        _ = ((dyadicPointUpTo (2 * T) (n + 1) (2 * cubeDyadicApproxIndex T (t.1 k) n) :
              NNReal) : ℝ) - T := by
              rw [dyadicPointUpTo_even]
        _ = (cubeFiberPoint
              (d := d)
              T
              (n + 1)
              i
              (cubeStepChainAnchor (d := d) T t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) (n + 1)) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n + 1) (i := i) (j := k)
                (a := cubeStepChainAnchor (d := d) T t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) (n + 1))
                hk']
              simp [cubeStepChainAnchor, i, hlt]

/-- Helper for Exercise 21.1.1: one step of the row-step chain is bounded by the interval
good-row estimate on the corresponding refined coordinate fiber. -/
private lemma cubeStepChainPoint_step_le_of_rowGood
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T : ℝ≥0) (q : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) (ω : Ω)
    (hgood : ω ∉ cubeDyadicRowBadEvent (d := d) X T q (n + 1)) :
    dist
        (X (cubeStepChainPoint (d := d) T t n (m + 1)).1 ω)
        (X (cubeStepChainPoint (d := d) T t n m).1 ω) ≤
      intervalDyadicStepThreshold q (n + 1) := by
  let i : Fin d := ⟨m, hm⟩
  let u : ℝ≥0 := Real.toNNReal (t.1 i + T)
  have hu_nonneg : 0 ≤ t.1 i + T := by
    linarith [(t.2 i).1]
  have hu_le : u ≤ 2 * T := by
    dsimp [u]
    rw [Real.toNNReal_of_nonneg hu_nonneg]
    change t.1 i + T ≤ (2 : ℝ) * T
    linarith [(t.2 i).2]
  have hfiberGood :
      ω ∉ cubeDyadicFiberBadEvent (d := d) X T q (n + 1) i
        (cubeStepChainAnchor (d := d) T t n m hm) := by
    -- Proof comment: the cube row-bad event is the union of all fiber bad events, so a good cube
    -- row is good on this particular coordinate fiber.
    intro hbad
    have hrowBad : ω ∈ cubeDyadicRowBadEvent (d := d) X T q (n + 1) := by
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨cubeStepChainAnchor (d := d) T t n m hm, hbad⟩⟩
    exact hgood hrowBad
  have hinterval :
      dist
          (X
            (cubeFiberPoint
              (d := d)
              T
              (n + 1)
              i
              (cubeStepChainAnchor (d := d) T t n m hm)
              (intervalClippedDyadicApprox (2 * T) u (n + 1))).1 ω)
          (X
            (cubeFiberPoint
              (d := d)
              T
              (n + 1)
              i
              (cubeStepChainAnchor (d := d) T t n m hm)
              (intervalClippedDyadicApprox (2 * T) u n)).1 ω) ≤
        intervalDyadicStepThreshold q (n + 1) := by
    exact intervalClippedDyadicApprox_step_le_of_rowGood
      (X := fun v ω ↦
        X
          (cubeFiberPoint
            (d := d)
            T
            (n + 1)
            i
            (cubeStepChainAnchor (d := d) T t n m hm)
            v).1 ω)
      (T := 2 * T)
      (q := q)
      (t := u)
      (n := n)
      hu_le
      hfiberGood
  -- Proof comment: rewrite the two fiber evaluations back to the neighboring chain points.
  rw [cubeStepChainPoint_eq_cubeFiberPoint_refined (d := d) T t n m hm,
    cubeStepChainPoint_eq_cubeFiberPoint_coarse (d := d) T t n m hm]
  simpa [i, u] using hinterval

/-- Helper for Exercise 21.1.1: a good refined cube row controls the full jump between successive
cube dyadic approximants by summing the `d` coordinate-fiber increments. -/
private lemma cubeClippedDyadicApprox_step_le_of_rowGood
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T : ℝ≥0) (q : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) (n : ℕ) (ω : Ω)
    (hgood : ω ∉ cubeDyadicRowBadEvent (d := d) X T q (n + 1)) :
    dist
        (X (cubeClippedDyadicApprox (d := d) T t (n + 1)).1 ω)
        (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) ≤
      (d : ℝ) * intervalDyadicStepThreshold q (n + 1) := by
  let f : ℕ → E := fun m ↦ X (cubeStepChainPoint (d := d) T t n m).1 ω
  have htel :
      dist (f 0) (f d) ≤
        ∑ m ∈ Finset.range d, dist (f m) (f (m + 1)) := by
    simpa [f] using dist_le_range_sum_dist (f := f) d
  have hsum :
      dist (f 0) (f d) ≤
        ∑ m ∈ Finset.range d, intervalDyadicStepThreshold q (n + 1) := by
    refine le_trans htel ?_
    refine Finset.sum_le_sum ?_
    intro m hm
    simpa [f, dist_comm] using
      cubeStepChainPoint_step_le_of_rowGood
        (d := d) X T q t n m (Finset.mem_range.mp hm) ω hgood
  have hconst :
      ∑ m ∈ Finset.range d, intervalDyadicStepThreshold q (n + 1) =
        (d : ℝ) * intervalDyadicStepThreshold q (n + 1) := by
    simp
  -- Proof comment: the chain starts at the coarse row and ends at the refined row, so the
  -- polygon inequality over the `d` coordinate updates gives the full row-step bound.
  calc
    dist
        (X (cubeClippedDyadicApprox (d := d) T t (n + 1)).1 ω)
        (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        =
      dist (f d) (f 0) := by
        simp [f, cubeStepChainPoint_zero, cubeStepChainPoint_all]
    _ = dist (f 0) (f d) := by rw [dist_comm]
    _ ≤ ∑ m ∈ Finset.range d, intervalDyadicStepThreshold q (n + 1) := hsum
    _ = (d : ℝ) * intervalDyadicStepThreshold q (n + 1) := hconst

/-- Helper for Exercise 21.1.1: the same-row pair chain replaces the first `m` row-`n`
coordinates of `s` by those of `t` and leaves the remaining coordinates unchanged. -/
private noncomputable def cubePairChainPoint
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) :
    euclideanClosedCube d (T : ℝ) :=
  ⟨WithLp.toLp 2 fun i : Fin d =>
      if i.1 < m then
        cubeClippedDyadicApproxCoordinate T (t.1 i) n
      else
        cubeClippedDyadicApproxCoordinate T (s.1 i) n, by
    intro i
    by_cases hi : i.1 < m
    · -- Proof comment: replaced coordinates use the row-`n` dyadic value from `t`, which still
      -- lies in the cube interval.
      simpa [hi] using
        cubeClippedDyadicApproxCoordinate_mem_Icc (T := T) (x := t.1 i) (n := n)
    · -- Proof comment: untouched coordinates retain the row-`n` dyadic value from `s`.
      simpa [hi] using
        cubeClippedDyadicApproxCoordinate_mem_Icc (T := T) (x := s.1 i) (n := n)⟩

/-- Helper for Exercise 21.1.1: the coordinate formula for the same-row pair chain is just the
defining piecewise replacement. -/
private lemma cubePairChainPoint_apply
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (i : Fin d) :
    (cubePairChainPoint (d := d) T s t n m : EuclideanSpace ℝ (Fin d)) i =
      if i.1 < m then
        cubeClippedDyadicApproxCoordinate T (t.1 i) n
      else
        cubeClippedDyadicApproxCoordinate T (s.1 i) n := by
  simp [cubePairChainPoint]

/-- Helper for Exercise 21.1.1: the same-row pair chain starts at the row-`n` approximant of
`s`. -/
private lemma cubePairChainPoint_zero
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n : ℕ) :
    cubePairChainPoint (d := d) T s t n 0 = cubeClippedDyadicApprox (d := d) T s n := by
  ext i
  -- Proof comment: with `m = 0`, the chain has not yet switched any coordinate from `s` to `t`.
  simp [cubePairChainPoint_apply, cubeClippedDyadicApprox_apply]

/-- Helper for Exercise 21.1.1: after replacing all `d` coordinates, the same-row pair chain lands
on the row-`n` approximant of `t`. -/
private lemma cubePairChainPoint_all
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n : ℕ) :
    cubePairChainPoint (d := d) T s t n d = cubeClippedDyadicApprox (d := d) T t n := by
  ext i
  -- Proof comment: every coordinate has been replaced by the row-`n` value from `t`.
  have hi : i.1 < d := i.2
  simp [cubePairChainPoint_apply, cubeClippedDyadicApprox_apply, hi]

/-- Helper for Exercise 21.1.1: the `m`-th same-row pair comparison is controlled by a row-`n`
coordinate fiber whose earlier coordinates use the row-`n` data of `t` and whose later
coordinates use the row-`n` data of `s`. -/
private noncomputable def cubePairChainAnchor
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) :
    cubeFiberAnchor (d := d) T n ⟨m, hm⟩ :=
  fun j =>
    if hj : j.1.1 < m then
      ⟨cubeDyadicApproxIndex T (t.1 j.1) n, by
        exact lt_of_le_of_lt
          (cubeDyadicApproxIndex_le_cutoff (d := d) T t n j.1)
          (Nat.lt_succ_self _)⟩
    else
      ⟨cubeDyadicApproxIndex T (s.1 j.1) n, by
        exact lt_of_le_of_lt
          (cubeDyadicApproxIndex_le_cutoff (d := d) T s n j.1)
          (Nat.lt_succ_self _)⟩

/-- Helper for Exercise 21.1.1: the `m`-th same-row pair chain point is the corresponding
row-`n` fiber point evaluated at the translated coordinate of `s`. -/
private lemma cubePairChainPoint_eq_cubeFiberPoint_source
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) :
    cubePairChainPoint (d := d) T s t n m =
      cubeFiberPoint
        (d := d)
        T
        n
        ⟨m, hm⟩
        (cubePairChainAnchor (d := d) T s t n m hm)
        (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (s.1 ⟨m, hm⟩ + T)) n) := by
  ext k
  let i : Fin d := ⟨m, hm⟩
  by_cases hk : k = i
  · subst hk
    -- Proof comment: on the varying coordinate, the pair chain still uses the source coordinate,
    -- which is exactly the translated row-`n` fiber parameter.
    simp [i, cubePairChainPoint_apply, cubeFiberPoint_apply_same, cubeClippedDyadicApproxCoordinate,
      intervalClippedDyadicApprox, clippedRightDyadicApprox]
  · have hk' : k ≠ i := hk
    by_cases hlt : k.1 < m
    · -- Proof comment: before the varying coordinate, the anchor stores the row-`n` dyadic data
      -- from `t`, which is exactly what the pair chain already uses.
      calc
        (cubePairChainPoint (d := d) T s t n m : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (t.1 k) n := by
                simp [cubePairChainPoint_apply, hlt]
        _ = ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (t.1 k) n) :
              NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := t.1 k) (t.2 k) n
        _ = (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (s.1 i + T)) n) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n) (i := i) (j := k)
                (a := cubePairChainAnchor (d := d) T s t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (s.1 i + T)) n)
                hk']
              simp [cubePairChainAnchor, i, hlt]
    · -- Proof comment: after the varying coordinate, the anchor keeps the row-`n` dyadic data
      -- from `s`, matching the unchanged coordinates of the pair chain.
      calc
        (cubePairChainPoint (d := d) T s t n m : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (s.1 k) n := by
                simp [cubePairChainPoint_apply, hlt]
        _ = ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (s.1 k) n) :
              NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := s.1 k) (s.2 k) n
        _ = (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (s.1 i + T)) n) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n) (i := i) (j := k)
                (a := cubePairChainAnchor (d := d) T s t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (s.1 i + T)) n)
                hk']
              simp [cubePairChainAnchor, i, hlt]

/-- Helper for Exercise 21.1.1: the next same-row pair chain point is the same row-`n` fiber
point evaluated at the translated coordinate of `t`. -/
private lemma cubePairChainPoint_eq_cubeFiberPoint_target
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) :
    cubePairChainPoint (d := d) T s t n (m + 1) =
      cubeFiberPoint
        (d := d)
        T
        n
        ⟨m, hm⟩
        (cubePairChainAnchor (d := d) T s t n m hm)
        (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 ⟨m, hm⟩ + T)) n) := by
  ext k
  let i : Fin d := ⟨m, hm⟩
  by_cases hk : k = i
  · subst hk
    -- Proof comment: on the varying coordinate, the successor pair-chain point has switched to
    -- the target coordinate, which is exactly the translated fiber parameter.
    simp [i, cubePairChainPoint_apply, cubeFiberPoint_apply_same, cubeClippedDyadicApproxCoordinate,
      intervalClippedDyadicApprox, clippedRightDyadicApprox]
  · have hk' : k ≠ i := hk
    have hk_ne_val : k.1 ≠ m := by
      intro hkval
      apply hk
      exact Fin.ext hkval
    by_cases hlt : k.1 < m
    · -- Proof comment: coordinates before the varying slot already use the target row-`n` data
      -- on both sides of the identification.
      calc
        (cubePairChainPoint (d := d) T s t n (m + 1) : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (t.1 k) n := by
                have hklt : k.1 < m + 1 := by omega
                simp [cubePairChainPoint_apply, hklt]
        _ = ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (t.1 k) n) :
              NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := t.1 k) (t.2 k) n
        _ = (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n) (i := i) (j := k)
                (a := cubePairChainAnchor (d := d) T s t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n)
                hk']
              simp [cubePairChainAnchor, i, hlt]
    · -- Proof comment: after the varying slot, the successor pair-chain point still uses the
      -- source row-`n` data, which is exactly what the fixed anchor stores there.
      calc
        (cubePairChainPoint (d := d) T s t n (m + 1) : EuclideanSpace ℝ (Fin d)) k
            = cubeClippedDyadicApproxCoordinate T (s.1 k) n := by
                have hnot : ¬ k.1 < m + 1 := by
                  omega
                simp [cubePairChainPoint_apply, hnot]
        _ = ((dyadicPointUpTo (2 * T) n (cubeDyadicApproxIndex T (s.1 k) n) :
              NNReal) : ℝ) - T := by
              exact cubeClippedDyadicApproxCoordinate_eq_dyadicPointUpTo_sub
                (T := T) (x := s.1 k) (s.2 k) n
        _ = (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n) :
                EuclideanSpace ℝ (Fin d)) k := by
              symm
              rw [cubeFiberPoint_apply_ne (d := d) (T := T) (n := n) (i := i) (j := k)
                (a := cubePairChainAnchor (d := d) T s t n m hm)
                (u := intervalClippedDyadicApprox (2 * T) (Real.toNNReal (t.1 i + T)) n)
                hk']
              simp [cubePairChainAnchor, i, hlt]

/-- Helper for Exercise 21.1.1: translating one cube coordinate into `[0, 2T]` does not enlarge
its distance beyond the ambient cube distance. -/
private lemma dist_translatedCubeCoordinate_le_dist
    (T : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (i : Fin d) :
    dist (Real.toNNReal (s.1 i + T)) (Real.toNNReal (t.1 i + T)) ≤ dist s t := by
  have hcoord :
      dist (s.1 i) (t.1 i) ≤
        dist ((s : euclideanClosedCube d (T : ℝ)) : EuclideanSpace ℝ (Fin d))
          ((t : euclideanClosedCube d (T : ℝ)) : EuclideanSpace ℝ (Fin d)) := by
    simpa [dist_eq_norm, sub_eq_add_neg] using abs_apply_le_norm (d := d) (s.1 - t.1) i
  have htranslated :
      dist (s.1 i + T) (t.1 i + T) ≤ dist s t := by
    calc
      dist (s.1 i + T) (t.1 i + T) = dist (s.1 i) (t.1 i) := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          dist_add_right (s.1 i) (t.1 i) T
      _ ≤ dist s t := by
            simpa using hcoord
  have htoNNReal :
      dist (Real.toNNReal (s.1 i + T)) (Real.toNNReal (t.1 i + T)) ≤
        dist (s.1 i + T) (t.1 i + T) := by
    simpa using (Real.lipschitzWith_toNNReal.dist_le_mul (s.1 i + T) (t.1 i + T))
  -- Proof comment: translating a coordinate by `+T` preserves its real distance, and the
  -- `toNNReal` projection cannot increase distance.
  exact le_trans htoNNReal htranslated

/-- Helper for Exercise 21.1.1: one same-row pair-chain step is bounded by the interval good-row
estimate on the corresponding row-`n` coordinate fiber. -/
private lemma cubePairChainPoint_step_le_of_rowGood_of_dist_le
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T : ℝ≥0) (q : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n m : ℕ) (hm : m < d) (ω : Ω)
    (hclose : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n)
    (hgood : ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    dist
        (X (cubePairChainPoint (d := d) T s t n (m + 1)).1 ω)
        (X (cubePairChainPoint (d := d) T s t n m).1 ω) ≤
      intervalDyadicStepThreshold q n := by
  let i : Fin d := ⟨m, hm⟩
  let us : ℝ≥0 := Real.toNNReal (s.1 i + T)
  let ut : ℝ≥0 := Real.toNNReal (t.1 i + T)
  have hus_nonneg : 0 ≤ s.1 i + T := by
    linarith [(s.2 i).1]
  have hut_nonneg : 0 ≤ t.1 i + T := by
    linarith [(t.2 i).1]
  have hus_le : us ≤ 2 * T := by
    dsimp [us]
    rw [Real.toNNReal_of_nonneg hus_nonneg]
    change s.1 i + T ≤ (2 : ℝ) * T
    linarith [(s.2 i).2]
  have hut_le : ut ≤ 2 * T := by
    dsimp [ut]
    rw [Real.toNNReal_of_nonneg hut_nonneg]
    change t.1 i + T ≤ (2 : ℝ) * T
    linarith [(t.2 i).2]
  have hcoord_close :
      dist us ut ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
    exact le_trans (dist_translatedCubeCoordinate_le_dist (d := d) T s t i) hclose
  have hfiberGood :
      ω ∉ cubeDyadicFiberBadEvent (d := d) X T q n i
        (cubePairChainAnchor (d := d) T s t n m hm) := by
    -- Proof comment: a good cube row is good on every fixed coordinate fiber appearing in that
    -- row.
    intro hbad
    have hrowBad : ω ∈ cubeDyadicRowBadEvent (d := d) X T q n := by
      exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨cubePairChainAnchor (d := d) T s t n m hm, hbad⟩⟩
    exact hgood hrowBad
  by_cases hst : us ≤ ut
  · have hinterval :
      dist
          (X
            (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) ut n)).1 ω)
          (X
            (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) us n)).1 ω) ≤
        intervalDyadicStepThreshold q n := by
      exact intervalClippedDyadicApprox_pair_le_of_rowGood_of_dist_le
        (X := fun u ω ↦
          X
            (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              u).1 ω)
        (T := 2 * T)
        (q := q)
        (s := us)
        (t := ut)
        (n := n)
        hus_le
        hut_le
        hst
        hcoord_close
        hfiberGood
    -- Proof comment: the ordered interval estimate now matches the pair-chain step after the two
    -- fiber identifications.
    rw [cubePairChainPoint_eq_cubeFiberPoint_target (d := d) T s t n m hm,
      cubePairChainPoint_eq_cubeFiberPoint_source (d := d) T s t n m hm]
    simpa [i, us, ut] using hinterval
  · have hts : ut ≤ us := le_of_not_ge hst
    have hinterval :
      dist
          (X
            (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) us n)).1 ω)
          (X
            (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              (intervalClippedDyadicApprox (2 * T) ut n)).1 ω) ≤
        intervalDyadicStepThreshold q n := by
      exact intervalClippedDyadicApprox_pair_le_of_rowGood_of_dist_le
        (X := fun u ω ↦
          X
            (cubeFiberPoint
              (d := d)
              T
              n
              i
              (cubePairChainAnchor (d := d) T s t n m hm)
              u).1 ω)
        (T := 2 * T)
        (q := q)
        (s := ut)
        (t := us)
        (n := n)
        hut_le
        hus_le
        hts
        (by simpa [dist_comm] using hcoord_close)
        hfiberGood
    have hinterval' :
        dist
            (X
              (cubeFiberPoint
                (d := d)
                T
                n
                i
                (cubePairChainAnchor (d := d) T s t n m hm)
                (intervalClippedDyadicApprox (2 * T) ut n)).1 ω)
            (X
              (cubeFiberPoint
                (d := d)
                T
                n
                i
                (cubePairChainAnchor (d := d) T s t n m hm)
                (intervalClippedDyadicApprox (2 * T) us n)).1 ω) ≤
          intervalDyadicStepThreshold q n := by
      simpa [dist_comm] using hinterval
    -- Proof comment: in the reversed-coordinate case, use symmetry of distance after applying the
    -- interval pair estimate in the ordered direction.
    rw [cubePairChainPoint_eq_cubeFiberPoint_target (d := d) T s t n m hm,
      cubePairChainPoint_eq_cubeFiberPoint_source (d := d) T s t n m hm]
    simpa [i, us, ut] using hinterval'

/-- Helper for Exercise 21.1.1: a good row controls the full same-row gap between two cube
dyadic approximants once the original cube points are within one dyadic mesh. -/
private lemma cubeClippedDyadicApprox_pair_le_of_rowGood_of_dist_le
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T : ℝ≥0) (q : ℝ≥0) (s t : euclideanClosedCube d (T : ℝ)) (n : ℕ) (ω : Ω)
    (hclose : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n)
    (hgood : ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    dist
        (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) ≤
      (d : ℝ) * intervalDyadicStepThreshold q n := by
  let f : ℕ → E := fun m ↦ X (cubePairChainPoint (d := d) T s t n m).1 ω
  have htel :
      dist (f 0) (f d) ≤
        ∑ m ∈ Finset.range d, dist (f m) (f (m + 1)) := by
    simpa [f] using dist_le_range_sum_dist (f := f) d
  have hsum :
      dist (f 0) (f d) ≤
        ∑ m ∈ Finset.range d, intervalDyadicStepThreshold q n := by
    refine le_trans htel ?_
    refine Finset.sum_le_sum ?_
    intro m hm
    simpa [f, dist_comm] using
      cubePairChainPoint_step_le_of_rowGood_of_dist_le
        (d := d) X T q s t n m (Finset.mem_range.mp hm) ω hclose hgood
  have hconst :
      ∑ m ∈ Finset.range d, intervalDyadicStepThreshold q n =
        (d : ℝ) * intervalDyadicStepThreshold q n := by
    simp
  -- Proof comment: the pair chain starts at the row-`n` approximant of `s` and ends at that of
  -- `t`, so summing the coordinate-fiber pair estimates gives the full same-row bound.
  calc
    dist
        (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
        =
      dist (f d) (f 0) := by
        simp [f, cubePairChainPoint_zero, cubePairChainPoint_all]
    _ = dist (f 0) (f d) := by rw [dist_comm]
    _ ≤ ∑ m ∈ Finset.range d, intervalDyadicStepThreshold q n := hsum
    _ = (d : ℝ) * intervalDyadicStepThreshold q n := hconst

/-- Helper for Exercise 21.1.1: the theorem-local cube dyadic approximants converge back to the
original cube point in the ambient Euclidean space. -/
private lemma tendsto_cubeClippedDyadicApprox_val
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) :
    Filter.Tendsto
      (fun n ↦ (cubeClippedDyadicApprox (d := d) T t n : EuclideanSpace ℝ (Fin d)))
      Filter.atTop
      (nhds (t : EuclideanSpace ℝ (Fin d))) := by
  have hpi :
      Filter.Tendsto
        (fun n : ℕ ↦ fun i : Fin d =>
          (cubeClippedDyadicApprox (d := d) T t n : EuclideanSpace ℝ (Fin d)) i)
        Filter.atTop
        (nhds fun i : Fin d => (t : EuclideanSpace ℝ (Fin d)) i) := by
    refine (tendsto_pi_nhds).2 ?_
    intro i
    -- Proof comment: on each coordinate, the translated interval dyadic approximation converges
    -- back to the original coordinate, and finite products are detected coordinatewise.
    simpa [cubeClippedDyadicApprox_apply] using
      tendsto_cubeClippedDyadicApproxCoordinate (T := T) (x := t.1 i) (t.2 i)
  have htoLp :
      Filter.Tendsto
        (fun n : ℕ ↦ WithLp.toLp (2 : ℝ≥0∞) fun i : Fin d =>
          (cubeClippedDyadicApprox (d := d) T t n : EuclideanSpace ℝ (Fin d)) i)
        Filter.atTop
        (nhds (WithLp.toLp (2 : ℝ≥0∞) fun i : Fin d =>
          (t : EuclideanSpace ℝ (Fin d)) i)) := by
    exact
      (PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin d => ℝ)).continuousAt.tendsto.comp
        hpi
  simpa using htoLp

/-- Helper for Exercise 21.1.1: the theorem-local cube dyadic approximants also converge on the
closed-cube subtype itself. -/
private lemma tendsto_cubeClippedDyadicApprox
    (T : ℝ≥0) (t : euclideanClosedCube d (T : ℝ)) :
    Filter.Tendsto (cubeClippedDyadicApprox (d := d) T t) Filter.atTop (nhds t) := by
  -- Proof comment: the cube subtype inherits its topology from the ambient Euclidean space, so
  -- the subtype convergence is exactly the ambient convergence of the coerced approximants.
  exact (tendsto_subtype_rng (x := t)).2 (tendsto_cubeClippedDyadicApprox_val (d := d) T t)

/-- Helper for Exercise 21.1.1: for one fixed cube point, the cube-owner Kolmogorov estimate and
Markov's inequality control the distance between the process at that point and at its theorem-local
dyadic cube approximants. -/
private lemma measureReal_cubeClippedDyadicApprox_dist_gt_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β T C : ℝ≥0}
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (t : euclideanClosedCube d (T : ℝ)) {ε : ℝ}
    (hε : 0 < ε) (n : ℕ) :
    μ.real {ω | ε < dist (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) (X t.1 ω)} ≤
      C *
          dist
            ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
              EuclideanSpace ℝ (Fin d))
            (t : EuclideanSpace ℝ (Fin d)) ^
            (((d : ℝ≥0) : ℝ) + β) /
        ε ^ (α : ℝ) := by
  let approx : euclideanClosedCube d (T : ℝ) := cubeClippedDyadicApprox (d := d) T t n
  have hαpos : 0 < (α : ℝ) := hC.p_pos
  have hq_nonneg : 0 ≤ (((d : ℝ≥0) : ℝ) + β) := by
    change 0 ≤ ((((d : ℝ≥0) + β : ℝ≥0) : ℝ))
    exact le_of_lt hC.q_pos
  have hM_nonneg :
      0 ≤
        C *
          dist (approx : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^
            (((d : ℝ≥0) : ℝ) + β) := by
    positivity
  have hmeas :
      AEMeasurable (fun ω ↦ edist (X approx.1 ω) (X t.1 ω) ^ (α : ℝ)) μ := by
    -- Proof comment: the cube-owner Kolmogorov hypothesis already gives measurability of every
    -- fixed increment on the cube subtype, so the powered distance is also a.e. measurable.
    exact ((hC.measurable_edist (s := approx) (t := t)).aemeasurable).pow_const (α : ℝ)
  have hlintegral :
      ∫⁻ ω, edist (X approx.1 ω) (X t.1 ω) ^ (α : ℝ) ∂μ ≤
        ENNReal.ofReal
          (C *
            dist (approx : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^
              (((d : ℝ≥0) : ℝ) + β)) := by
    -- Proof comment: apply the cube-owner increment estimate to the approximant and the target,
    -- then rewrite the ambient `edist` power into a real-valued bound for Markov's inequality.
    calc
      ∫⁻ ω, edist (X approx.1 ω) (X t.1 ω) ^ (α : ℝ) ∂μ ≤
          (C : ℝ≥0∞) *
            edist (approx : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^
              (((d : ℝ≥0) : ℝ) + β) := by
        simpa [approx] using hC.increment_lintegral_le (s := t.1) (t := approx.1) t.2 approx.2
      _ =
          (C : ℝ≥0∞) *
            ENNReal.ofReal
              (dist (approx : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^
                (((d : ℝ≥0) : ℝ) + β)) := by
            rw [edist_dist,
              ENNReal.ofReal_rpow_of_nonneg
                (dist_nonneg : 0 ≤
                  dist (approx : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)))
                hq_nonneg]
      _ =
          ENNReal.ofReal
            (C *
              dist (approx : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)) ^
                (((d : ℝ≥0) : ℝ) + β)) := by
            simp [ENNReal.ofReal_mul]
  -- Proof comment: the fixed-time cube approximant estimate is now exactly the abstract
  -- distance-tail bound from `measureReal_edist_gt_le_of_lintegral_bound`.
  simpa [approx] using
    measureReal_edist_gt_le_of_lintegral_bound
      (μ := μ)
      (Y := fun ω ↦ X approx.1 ω)
      (Z := fun ω ↦ X t.1 ω)
      (hα := hαpos)
      (hδ := hε)
      (hM := hM_nonneg)
      hmeas
      hlintegral

/-- Helper for Exercise 21.1.1: for one fixed cube point, the theorem-local dyadic cube
approximants converge in measure to the original process value. -/
private lemma tendstoInMeasure_cubeClippedDyadicApprox_to_original
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β T C : ℝ≥0}
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (t : euclideanClosedCube d (T : ℝ)) :
    TendstoInMeasure μ
      (fun n ω ↦ X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
      Filter.atTop
      (fun ω ↦ X t.1 ω) := by
  refine (MeasureTheory.tendstoInMeasure_iff_measureReal_dist).2 ?_
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    positivity
  have hpointwise :
      ∀ n : ℕ,
        μ.real {ω | ε ≤ dist (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) (X t.1 ω)} ≤
          C *
            dist
              ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))
              (t : EuclideanSpace ℝ (Fin d)) ^
              (((d : ℝ≥0) : ℝ) + β) /
            ε' ^ (α : ℝ) := by
    intro n
    have hsubset :
        {ω | ε ≤ dist (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) (X t.1 ω)} ⊆
          {ω | ε' < dist (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) (X t.1 ω)} := by
      intro ω hω
      dsimp [ε'] at *
      linarith
    -- Proof comment: shrink the threshold from `ε` to `ε / 2` so the strict-tail Markov estimate
    -- applies, then reuse the fixed-time cube approximation bound.
    calc
      μ.real {ω | ε ≤ dist (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) (X t.1 ω)}
          ≤
            μ.real {ω | ε' < dist (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) (X t.1 ω)} :=
        MeasureTheory.measureReal_mono hsubset
      _ ≤
          C *
            dist
              ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))
              (t : EuclideanSpace ℝ (Fin d)) ^
              (((d : ℝ≥0) : ℝ) + β) /
            ε' ^ (α : ℝ) :=
        measureReal_cubeClippedDyadicApprox_dist_gt_le
          (d := d) (μ := μ) (X := X) (α := α) (β := β) (T := T) (C := C) hC t hε' n
  have hdist :
      Filter.Tendsto
        (fun n ↦
          dist
            ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
              EuclideanSpace ℝ (Fin d))
            (t : EuclideanSpace ℝ (Fin d)))
        Filter.atTop
        (nhds 0) := by
    have hdist' :
        Filter.Tendsto
          (fun n ↦
            dist
              ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))
              (t : EuclideanSpace ℝ (Fin d)))
          Filter.atTop
          (nhds
            (dist (t : EuclideanSpace ℝ (Fin d)) (t : EuclideanSpace ℝ (Fin d)))) := by
      exact (tendsto_cubeClippedDyadicApprox_val (d := d) T t).dist tendsto_const_nhds
    simpa using hdist'
  have hq_pos : 0 < (((d : ℝ≥0) : ℝ) + β) := by
    change 0 < ((((d : ℝ≥0) + β : ℝ≥0) : ℝ))
    exact hC.q_pos
  have hpow :
      Filter.Tendsto
        (fun n ↦
          dist
            ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
              EuclideanSpace ℝ (Fin d))
            (t : EuclideanSpace ℝ (Fin d)) ^
            (((d : ℝ≥0) : ℝ) + β))
        Filter.atTop
        (nhds 0) := by
    -- Proof comment: once the ambient cube mesh tends to `0`, the positive Kolmogorov exponent
    -- preserves that convergence after applying the real power.
    have hpow' :
        Filter.Tendsto
          (fun n ↦
            dist
              ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))
              (t : EuclideanSpace ℝ (Fin d)) ^
              (((d : ℝ≥0) : ℝ) + β))
          Filter.atTop
          (nhds ((0 : ℝ) ^ ((((d : ℝ≥0) + β : ℝ≥0) : ℝ)))) :=
      hdist.rpow_const (Or.inr hq_pos.le)
    convert hpow' using 2
    exact (Real.zero_rpow hq_pos.ne').symm
  have hupper :
      Filter.Tendsto
        (fun n ↦
          C *
            dist
              ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
                EuclideanSpace ℝ (Fin d))
              (t : EuclideanSpace ℝ (Fin d)) ^
              (((d : ℝ≥0) : ℝ) + β) /
            ε' ^ (α : ℝ))
        Filter.atTop
        (nhds 0) := by
    -- Proof comment: the Markov upper bound is a constant multiple of the vanishing mesh power.
    have hupper' :
        Filter.Tendsto
          (fun n ↦
            (C / ε' ^ (α : ℝ)) *
              dist
                ((cubeClippedDyadicApprox (d := d) T t n : euclideanClosedCube d (T : ℝ)) :
                  EuclideanSpace ℝ (Fin d))
                (t : EuclideanSpace ℝ (Fin d)) ^
                (((d : ℝ≥0) : ℝ) + β))
          Filter.atTop
          (nhds 0) := by
      simpa [zero_mul] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ ↦ C / ε' ^ (α : ℝ)) Filter.atTop
            (nhds (C / ε' ^ (α : ℝ)))).mul hpow
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper'
  exact
    squeeze_zero'
      (Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg)
      (Filter.Eventually.of_forall hpointwise)
      hupper

/-- Helper for Exercise 21.1.1: almost-sure convergence of a metric-valued dyadic extension
identifies it with the original process once the same approximants also converge in measure to the
original path value. -/
private lemma aeEq_original_of_metricDyadicExtension
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {S : Type*}
    {X Y : S → Ω → E} {t : S} {d : ℕ → S}
    (hd_meas : ∀ n, AEStronglyMeasurable (fun ω ↦ X (d n) ω) μ)
    (hd_ae :
      ∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ X (d n) ω) Filter.atTop (nhds (Y t ω)))
    (hd_measure :
      TendstoInMeasure μ (fun n ω ↦ X (d n) ω) Filter.atTop (fun ω ↦ X t ω)) :
    X t =ᵐ[μ] Y t := by
  -- Proof comment: convergence almost everywhere upgrades to convergence in measure, and the
  -- limit in measure is unique up to almost-everywhere equality.
  have hY_measure :
      TendstoInMeasure μ (fun n ω ↦ X (d n) ω) Filter.atTop (fun ω ↦ Y t ω) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_ae hd_meas hd_ae
  simpa using MeasureTheory.tendstoInMeasure_ae_unique hd_measure hY_measure

/-- Helper for Exercise 21.1.1: the interval row threshold is also the `q`-th power of the dyadic
mesh `(1 / 2)^n`. -/
private lemma intervalDyadicStepThreshold_eq_meshRpow
    (q : ℝ≥0) (n : ℕ) :
    intervalDyadicStepThreshold q n = ((1 / 2 : ℝ) ^ n) ^ (q : ℝ) := by
  -- Proof comment: rewrite `2^{-qn}` first as `(2^{-q})^n`, then swap the natural and real
  -- powers on the dyadic mesh.
  calc
    intervalDyadicStepThreshold q n = ((2 : ℝ) ^ (-(q : ℝ))) ^ n :=
      intervalDyadicStepThreshold_eq_geomRatio_pow q n
    _ = (((1 / 2 : ℝ) ^ (q : ℝ))) ^ n := by
      congr 1
      calc
        (2 : ℝ) ^ (-(q : ℝ)) = ((2 : ℝ)⁻¹) ^ (q : ℝ) := by
          rw [Real.rpow_neg_eq_inv_rpow]
        _ = (1 / 2 : ℝ) ^ (q : ℝ) := by norm_num
    _ = ((1 / 2 : ℝ) ^ n) ^ (q : ℝ) := by
      exact Real.rpow_pow_comm (by positivity : 0 ≤ (1 / 2 : ℝ)) (q : ℝ) n

/-- Helper for Exercise 21.1.1: if all cube rows from `N` onward are good at `ω`, then the
shifted cube dyadic approximants have geometric one-step decay. -/
private lemma cubeClippedDyadicApprox_step_le_geometric_of_rowGoodFrom
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    {t : euclideanClosedCube d (T : ℝ)}
    (_hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    ∀ n : ℕ,
      dist
          (X (cubeClippedDyadicApprox (d := d) T t (n + N + 1)).1 ω)
          (X (cubeClippedDyadicApprox (d := d) T t (n + N)).1 ω) ≤
        ((d : ℝ) * ((2 : ℝ) ^ (-(q : ℝ))) ^ (N + 1)) *
          ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
  intro n
  have hgood : ω ∉ cubeDyadicRowBadEvent (d := d) X T q (n + N + 1) := by
    exact hrows (n + N + 1) (by omega)
  have hstep :=
    cubeClippedDyadicApprox_step_le_of_rowGood
      (d := d) X T q t (n + N) ω hgood
  have hpow :
      (d : ℝ) * intervalDyadicStepThreshold q (n + N + 1) =
        ((d : ℝ) * ((2 : ℝ) ^ (-(q : ℝ))) ^ (N + 1)) *
          ((2 : ℝ) ^ (-(q : ℝ))) ^ n := by
    rw [intervalDyadicStepThreshold_eq_geomRatio_pow]
    have hadd : n + N + 1 = (N + 1) + n := by omega
    rw [hadd, pow_add]
    ring
  -- Proof comment: the row-good step estimate is exactly the geometric decay needed for the
  -- Cauchy criterion once the row index is shifted by `N`.
  rw [hpow] at hstep
  simpa [Nat.add_assoc, dist_comm] using hstep

/-- Helper for Exercise 21.1.1: good cube rows from `N` onward force the shifted dyadic
approximants to be Cauchy. -/
private lemma cauchySeq_cubeClippedDyadicApprox_of_rowGoodFrom
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    {t : euclideanClosedCube d (T : ℝ)}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    CauchySeq (fun n ↦ X (cubeClippedDyadicApprox (d := d) T t (n + N)).1 ω) := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hq_real : 0 < (q : ℝ) := by
    exact_mod_cast hq0
  have hr : r < 1 := by
    -- Proof comment: the geometric ratio is `2^{-q}`, strictly below `1` because `q > 0`.
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  -- Proof comment: apply the geometric Cauchy criterion to the shifted approximant sequence.
  exact
    cauchySeq_of_le_geometric
      (f := fun n ↦ X (cubeClippedDyadicApprox (d := d) T t (n + N)).1 ω)
      (r := r)
      (C := (d : ℝ) * r ^ (N + 1))
      hr
      (by
        intro n
        have hadd : n + N + 1 = n + 1 + N := by omega
        simpa [r, hadd, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
          mul_assoc, mul_left_comm, mul_comm, dist_comm] using
          cubeClippedDyadicApprox_step_le_geometric_of_rowGoodFrom
            (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t)
            hq0 hrows n)

/-- Helper for Exercise 21.1.1: package the good-row cube limit by choosing the limit of the
shifted Cauchy sequence of dyadic approximants. -/
private noncomputable def cubeGoodRowLimitPath
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T q : ℝ≥0) (hq0 : 0 < q) (ω : Ω) (N : ℕ)
    (hrows : ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n)
    (t : euclideanClosedCube d (T : ℝ)) : E :=
  Classical.choose <|
    cauchySeq_tendsto_of_complete <|
      cauchySeq_cubeClippedDyadicApprox_of_rowGoodFrom
        (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t)
        hq0 hrows

/-- Helper for Exercise 21.1.1: the shifted cube dyadic approximants converge to the packaged
good-row limit path. -/
private lemma tendsto_cubeGoodRowLimitPath_of_rowGoodFrom
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    {t : euclideanClosedCube d (T : ℝ)}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    Filter.Tendsto
      (fun n ↦ X (cubeClippedDyadicApprox (d := d) T t (n + N)).1 ω)
      Filter.atTop
      (nhds (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)) := by
  -- Proof comment: the limit path was defined by choosing the limit of this shifted Cauchy
  -- sequence, so the convergence proof is exactly the witness returned by completeness.
  simpa [cubeGoodRowLimitPath] using
    (Classical.choose_spec <|
      cauchySeq_tendsto_of_complete <|
        cauchySeq_cubeClippedDyadicApprox_of_rowGoodFrom
          (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t)
          hq0 hrows)

/-- Helper for Exercise 21.1.1: once the cube rows are good from `N` onward, every later dyadic
approximant stays within the geometric tail of the chosen good-row limit path. -/
private lemma dist_cubeClippedDyadicApprox_cubeGoodRowLimitPath_le_of_rowGoodFrom
    {X : EuclideanSpace ℝ (Fin d) → Ω → E} {T q : ℝ≥0} {ω : Ω} {N : ℕ}
    {t : euclideanClosedCube d (T : ℝ)}
    (hq0 : 0 < q)
    (hrows : ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n)
    {n : ℕ} (hn : N ≤ n) :
    dist
        (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) ≤
      (d : ℝ) * ((2 : ℝ) ^ (-(q : ℝ))) ^ (n + 1) /
        (1 - (2 : ℝ) ^ (-(q : ℝ))) := by
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hq_real : 0 < (q : ℝ) := by
    exact_mod_cast hq0
  have hr : r < 1 := by
    -- Proof comment: the good-row geometric ratio `2^{-q}` lies strictly below `1`.
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  let f : ℕ → E := fun m ↦ X (cubeClippedDyadicApprox (d := d) T t (m + N)).1 ω
  have hstep :
      ∀ m : ℕ, dist (f m) (f (m + 1)) ≤ ((d : ℝ) * r ^ (N + 1)) * r ^ m := by
    -- Proof comment: the shifted sequence inherits the geometric step estimate from the row-good
    -- hypothesis.
    intro m
    simpa [f, r, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
      mul_assoc, mul_left_comm, mul_comm, dist_comm] using
      cubeClippedDyadicApprox_step_le_geometric_of_rowGoodFrom
        (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows m
  have hlim :
      Filter.Tendsto f Filter.atTop
        (nhds (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)) := by
    -- Proof comment: this is the defining convergence of the chosen good-row limit path.
    simpa [f] using
      tendsto_cubeGoodRowLimitPath_of_rowGoodFrom
        (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows
  have hshift :
      dist
          (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
          (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) ≤
        ((d : ℝ) * r ^ (N + 1)) * r ^ (n - N) / (1 - r) := by
    -- Proof comment: apply the standard geometric tail estimate at the shifted index `n - N`.
    simpa [f, Nat.sub_add_cancel hn] using
      dist_le_of_le_geometric_of_tendsto
        (f := f)
        (r := r)
        (C := (d : ℝ) * r ^ (N + 1))
        hr
        hstep
        hlim
        (n - N)
  have hpow' : r ^ (N + 1) * r ^ (n - N) = r ^ (n + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hpow : ((d : ℝ) * r ^ (N + 1)) * r ^ (n - N) = (d : ℝ) * r ^ (n + 1) := by
    calc
      ((d : ℝ) * r ^ (N + 1)) * r ^ (n - N) = (d : ℝ) * (r ^ (N + 1) * r ^ (n - N)) := by
        ring
      _ = (d : ℝ) * r ^ (n + 1) := by rw [hpow']
  calc
    dist
        (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)
        ≤ ((d : ℝ) * r ^ (N + 1)) * r ^ (n - N) / (1 - r) := hshift
    _ = (d : ℝ) * r ^ (n + 1) / (1 - r) := by rw [hpow]
    _ = (d : ℝ) * ((2 : ℝ) ^ (-(q : ℝ))) ^ (n + 1) /
          (1 - (2 : ℝ) ^ (-(q : ℝ))) := by
          rfl

/-- Helper for Exercise 21.1.1: package the good-row cube version into one symbol so the main
theorem can reuse the same branch both for fixed-time almost-sure equality and for pathwise local
Hölder bounds. -/
private noncomputable def cubeGoodRowVersion
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T q : ℝ≥0) (hq0 : 0 < q)
    (t : euclideanClosedCube d (T : ℝ)) (ω : Ω) : E :=
  letI : Decidable (∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :=
    Classical.propDecidable _
  if hgood : ∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n then
    let N := eventualCubeGoodRowStart (d := d) (X := X) (T := T) (q := q) hgood
    cubeGoodRowLimitPath
      (d := d)
      X
      T
      q
      hq0
      ω
      N
      (eventualCubeGoodRowStart_spec (d := d) (X := X) (T := T) (q := q) hgood)
      t
  else
    X 0 ω

/-- Helper for Exercise 21.1.1: on almost every sample path, the theorem-local cube dyadic
approximants converge to the packaged good-row version at each fixed cube point. -/
private lemma ae_tendsto_cubeClippedDyadicApprox_to_cubeGoodRowVersion
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {T q : ℝ≥0}
    (hq0 : 0 < q)
    (hgood_ae :
      ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n)
    (t : euclideanClosedCube d (T : ℝ)) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n ↦ X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        Filter.atTop
        (nhds (cubeGoodRowVersion (d := d) X T q hq0 t ω)) := by
  filter_upwards [hgood_ae] with ω hgood
  let N : ℕ := eventualCubeGoodRowStart (d := d) (X := X) (T := T) (q := q) hgood
  have hrows :
      ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n :=
    eventualCubeGoodRowStart_spec (d := d) (X := X) (T := T) (q := q) hgood
  have hshift :
      Filter.Tendsto
        (fun n ↦ X (cubeClippedDyadicApprox (d := d) T t (n + N)).1 ω)
        Filter.atTop
        (nhds (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)) :=
    tendsto_cubeGoodRowLimitPath_of_rowGoodFrom
      (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows
  have hfull :
      Filter.Tendsto
        (fun n ↦ X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
        Filter.atTop
        (nhds (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)) := by
    -- Proof comment: dropping finitely many initial dyadic levels does not change the limit.
    exact (Filter.tendsto_add_atTop_iff_nat
      (f := fun n ↦ X (cubeClippedDyadicApprox (d := d) T t n).1 ω) N).mp <| by
        simpa [N] using hshift
  simpa [cubeGoodRowVersion, hgood, N] using hfull

/-- Helper for Exercise 21.1.1: at each fixed cube point, the packaged good-row version agrees
almost everywhere with the original process value. -/
private lemma aeEq_original_of_cubeGoodRowVersionAt
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β q T C : ℝ≥0}
    (hq0 : 0 < q)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    (hgood_ae :
      ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n)
    (t : euclideanClosedCube d (T : ℝ)) :
    X t.1 =ᵐ[μ] cubeGoodRowVersion (d := d) X T q hq0 t := by
  have hd_meas :
      ∀ n : ℕ,
        AEStronglyMeasurable
          (fun ω ↦ X (cubeClippedDyadicApprox (d := d) T t n).1 ω) μ := by
    intro n
    -- Proof comment: each fixed cube dyadic approximant is just evaluation of the cube-owner
    -- process at another cube point.
    let _ : MeasurableSpace E := borel E
    let _ : BorelSpace E := ⟨rfl⟩
    simpa using
      (hC.measurable (cubeClippedDyadicApprox (d := d) T t n)).aestronglyMeasurable
  -- Proof comment: the same dyadic approximants converge almost surely to the packaged version
  -- and in measure to the original process value.
  exact
    aeEq_original_of_metricDyadicExtension
      (μ := μ)
      (X := fun s ω ↦ X s.1 ω)
      (Y := cubeGoodRowVersion (d := d) X T q hq0)
      (t := t)
      (d := cubeClippedDyadicApprox (d := d) T t)
      hd_meas
      (ae_tendsto_cubeClippedDyadicApprox_to_cubeGoodRowVersion
        (d := d) (μ := μ) (X := X) (T := T) (q := q) hq0 hgood_ae t)
      (tendstoInMeasure_cubeClippedDyadicApprox_to_original
        (d := d) (μ := μ) (X := X) (α := α) (β := β) (T := T) (C := C) hC t)

/-- Helper for Exercise 21.1.1: every positive distance at most `1` sits between two successive
dyadic mesh sizes. -/
private lemma existsDyadicLevel_of_pos_dist_le_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∃ n : ℕ, (1 / 2 : ℝ) ^ (n + 1) < r ∧ r ≤ (1 / 2 : ℝ) ^ n := by
  -- Proof comment: this is the standard Archimedean dyadic scale choice on `(0, 1]`.
  simpa using
    exists_nat_pow_near_of_lt_one
      hr0
      hr1
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show (1 / 2 : ℝ) < 1 by norm_num)

/-- Helper for Exercise 21.1.1: on a good sample path, the packaged cube version is locally
Hölder on sufficiently small balls. -/
private lemma locallyHolderWith_cubeGoodRowVersion_of_goodBranch
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {T q : ℝ≥0} {ω : Ω}
    (hq0 : 0 < q)
    (hgood : ∀ᶠ n in Filter.atTop, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n) :
    LocallyHolderWith q (fun t : euclideanClosedCube d (T : ℝ) ↦
      cubeGoodRowVersion (d := d) X T q hq0 t ω) := by
  let N : ℕ := eventualCubeGoodRowStart (d := d) (X := X) (T := T) (q := q) hgood
  have hrows :
      ∀ n ≥ N, ω ∉ cubeDyadicRowBadEvent (d := d) X T q n :=
    eventualCubeGoodRowStart_spec (d := d) (X := X) (T := T) (q := q) hgood
  let r : ℝ := (2 : ℝ) ^ (-(q : ℝ))
  have hq_real : 0 < (q : ℝ) := by
    exact_mod_cast hq0
  have hr_pos : 0 < r := by
    dsimp [r]
    positivity
  have hr_lt_one : r < 1 := by
    -- Proof comment: the dyadic ratio `2^{-q}` is strictly less than `1`.
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : 1 < (2 : ℝ)) (by linarith)
  have hden_pos : 0 < 1 - r := by
    linarith
  let K : ℝ≥0 := ⟨(d : ℝ) * (1 + r) / (r * (1 - r)), by positivity⟩
  intro x
  refine ⟨Metric.ball x ((1 / 2 : ℝ) ^ (N + 2)), Metric.ball_mem_nhds _ (by positivity), K, ?_⟩
  intro s hs t ht
  by_cases hst0 : dist s t = 0
  · -- Proof comment: zero distance makes the Hölder estimate tautological.
    have hst_eq : s = t := dist_eq_zero.mp hst0
    simp [hst_eq]
  · have hst_pos : 0 < dist s t := by
      have hne : 0 ≠ dist s t := by
        simpa [eq_comm] using hst0
      exact lt_of_le_of_ne dist_nonneg hne
    have hsx : dist s x < (1 / 2 : ℝ) ^ (N + 2) := Metric.mem_ball.1 hs
    have hxt : dist x t < (1 / 2 : ℝ) ^ (N + 2) := by
      simpa [dist_comm] using Metric.mem_ball.1 ht
    have hsmall : dist s t ≤ (1 / 2 : ℝ) ^ (N + 1) := by
      have hsum :
          dist s x + dist x t < (1 / 2 : ℝ) ^ (N + 2) + (1 / 2 : ℝ) ^ (N + 2) := by
        linarith
      have hst_lt : dist s t < (1 / 2 : ℝ) ^ (N + 1) := by
        calc
          dist s t ≤ dist s x + dist x t := dist_triangle _ _ _
          _ < (1 / 2 : ℝ) ^ (N + 2) + (1 / 2 : ℝ) ^ (N + 2) := hsum
          _ = (1 / 2 : ℝ) ^ (N + 1) := by
                rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
                ring
      exact le_of_lt hst_lt
    have hone : dist s t ≤ (1 : ℝ) := by
      calc
        dist s t ≤ (1 / 2 : ℝ) ^ (N + 1) := hsmall
        _ ≤ 1 := by
              simpa using
                (pow_le_one₀ (show 0 ≤ (1 / 2 : ℝ) by norm_num)
                  (show (1 / 2 : ℝ) ≤ 1 by norm_num) :
                  (1 / 2 : ℝ) ^ (N + 1) ≤ 1)
    let xratio : ℝ := dist s t / ((1 / 2 : ℝ) ^ (N + 1))
    have hx_pos : 0 < xratio := by
      dsimp [xratio]
      positivity
    have hx_le_one : xratio ≤ 1 := by
      have hpow_pos : 0 < ((1 / 2 : ℝ) ^ (N + 1)) := by positivity
      exact (div_le_iff₀ hpow_pos).2 <| by
        simpa using hsmall
    obtain ⟨m, hm_lt, hm_le⟩ :=
      exists_nat_pow_near_of_lt_one
        hx_pos
        hx_le_one
        (show 0 < (1 / 2 : ℝ) by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num)
    let n : ℕ := N + 1 + m
    have hn : N ≤ n := by
      dsimp [n]
      omega
    have hupper : dist s t ≤ (1 / 2 : ℝ) ^ n := by
      have hpow_pos : 0 < ((1 / 2 : ℝ) ^ (N + 1)) := by positivity
      have hmul := (div_le_iff₀ hpow_pos).mp hm_le
      dsimp [xratio, n] at hmul ⊢
      have hn_eq : n = m + (N + 1) := by
        dsimp [n]
        omega
      calc
        dist s t ≤ ((1 / 2 : ℝ) ^ m) * ((1 / 2 : ℝ) ^ (N + 1)) := hmul
        _ = (1 / 2 : ℝ) ^ n := by
              simpa [hn_eq, pow_add, mul_comm]
    have hlower : (1 / 2 : ℝ) ^ (n + 1) < dist s t := by
      have hpow_pos : 0 < ((1 / 2 : ℝ) ^ (N + 1)) := by positivity
      have hmul := (lt_div_iff₀ hpow_pos).mp hm_lt
      dsimp [xratio, n] at hmul ⊢
      calc
        (1 / 2 : ℝ) ^ (n + 1)
            = ((1 / 2 : ℝ) ^ (m + 1)) * ((1 / 2 : ℝ) ^ (N + 1)) := by
                rw [show N + 1 + m + 1 = (m + 1) + (N + 1) by omega, pow_add]
        _ < dist s t := hmul
    have hs_tail :
        dist
            (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s) ≤
          (d : ℝ) * r ^ (n + 1) / (1 - r) := by
      simpa [r] using
        dist_cubeClippedDyadicApprox_cubeGoodRowLimitPath_le_of_rowGoodFrom
          (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := s) hq0 hrows hn
    have ht_tail :
        dist
            (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) ≤
          (d : ℝ) * r ^ (n + 1) / (1 - r) := by
      simpa [r] using
        dist_cubeClippedDyadicApprox_cubeGoodRowLimitPath_le_of_rowGoodFrom
          (d := d) (X := X) (T := T) (q := q) (ω := ω) (N := N) (t := t) hq0 hrows hn
    have hpair :
        dist
            (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
            (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) ≤
          (d : ℝ) * r ^ n := by
      have hgoodn : ω ∉ cubeDyadicRowBadEvent (d := d) X T q n := hrows n hn
      have hupper' : dist s t ≤ (1 : ℝ) / (2 : ℝ) ^ n := by
        simpa [one_div] using hupper
      simpa [r, intervalDyadicStepThreshold_eq_geomRatio_pow] using
        cubeClippedDyadicApprox_pair_le_of_rowGood_of_dist_le
          (d := d) X T q s t n ω hupper' hgoodn
    have htriangle :
        dist
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) ≤
          dist
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
              (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) := by
      calc
        dist
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)
            ≤
          dist
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) := by
                exact dist_triangle _ _ _
        _ ≤
          dist
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) +
            (dist
                (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
                (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) +
              dist
                (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
                (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)) := by
                  gcongr
                  exact dist_triangle _ _ _
        _ =
          dist
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
              (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) := by
                ring
    have hsmall_row :
        dist
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) ≤
          ((d : ℝ) * (1 + r) / (1 - r)) * r ^ n := by
      calc
        dist
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)
            ≤
          dist
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T s n).1 ω)
              (X (cubeClippedDyadicApprox (d := d) T t n).1 ω) +
            dist
              (X (cubeClippedDyadicApprox (d := d) T t n).1 ω)
              (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) := htriangle
        _ ≤ (d : ℝ) * r ^ (n + 1) / (1 - r) + (d : ℝ) * r ^ n +
              (d : ℝ) * r ^ (n + 1) / (1 - r) := by
              exact add_le_add
                (add_le_add
                  (by simpa [dist_comm] using hs_tail)
                  (by simpa [dist_comm] using hpair))
                ht_tail
        _ = ((d : ℝ) * (1 + r) / (1 - r)) * r ^ n := by
              have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
              rw [pow_succ]
              field_simp [hden_ne]
              ring
    have hpow_lt :
        r ^ (n + 1) < dist s t ^ (q : ℝ) := by
      have hpow_lt' :
          ((1 / 2 : ℝ) ^ (n + 1)) ^ (q : ℝ) < dist s t ^ (q : ℝ) :=
        Real.rpow_lt_rpow
          (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (n + 1))
          hlower
          hq_real
      calc
        r ^ (n + 1) = ((1 / 2 : ℝ) ^ (n + 1)) ^ (q : ℝ) := by
            rw [show r = (2 : ℝ) ^ (-(q : ℝ)) by rfl,
              ← intervalDyadicStepThreshold_eq_geomRatio_pow (q := q) (n := n + 1),
              intervalDyadicStepThreshold_eq_meshRpow (q := q) (n := n + 1)]
        _ < dist s t ^ (q : ℝ) := hpow_lt'
    have hrn_le :
        r ^ n ≤ dist s t ^ (q : ℝ) / r := by
      refine (le_div_iff₀ hr_pos).2 ?_
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hpow_lt.le
    have hreal :
        dist
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t) ≤
          (K : ℝ) * dist s t ^ (q : ℝ) := by
      calc
        dist
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
            (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)
            ≤ ((d : ℝ) * (1 + r) / (1 - r)) * r ^ n := hsmall_row
        _ ≤ ((d : ℝ) * (1 + r) / (1 - r)) * (dist s t ^ (q : ℝ) / r) := by
              gcongr
        _ = (K : ℝ) * dist s t ^ (q : ℝ) := by
              dsimp [K]
              have hden_ne : (1 - r) ≠ 0 := hden_pos.ne'
              field_simp [hr_pos.ne', hden_ne]
    have hpow :
        ENNReal.ofReal (dist s t ^ (q : ℝ)) =
          ENNReal.ofReal (dist s t) ^ (q : ℝ) := by
      exact (ENNReal.ofReal_rpow_of_nonneg (dist_nonneg : 0 ≤ dist s t) q.2).symm
    -- Proof comment: once the real Hölder bound is established, cast it to `ENNReal` and
    -- normalize the distance term into the `HolderOnWith` shape.
    calc
      edist
          (cubeGoodRowVersion (d := d) X T q hq0 s ω)
          (cubeGoodRowVersion (d := d) X T q hq0 t ω)
          = ENNReal.ofReal
              (dist
                (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows s)
                (cubeGoodRowLimitPath (d := d) X T q hq0 ω N hrows t)) := by
                  simp [cubeGoodRowVersion, hgood, N, edist_dist]
      _ ≤ ENNReal.ofReal ((K : ℝ) * dist s t ^ (q : ℝ)) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (K : ℝ) * ENNReal.ofReal (dist s t ^ (q : ℝ)) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (K : ℝ))]
      _ = (K : ℝ≥0∞) * ENNReal.ofReal (dist s t ^ (q : ℝ)) := by
            rw [ENNReal.ofReal_coe_nnreal]
      _ = (K : ℝ≥0∞) * (ENNReal.ofReal (dist s t) ^ (q : ℝ)) := by
            exact congrArg (fun z : ℝ≥0∞ ↦ (K : ℝ≥0∞) * z) hpow
      _ = (K : ℝ≥0∞) * edist s t ^ (q : ℝ) := by
            rw [edist_dist]

/-- Helper for Exercise 21.1.1: after removing the degenerate radius `T = 0`, the positive-radius
cube theorem should first construct a locally Hölder version on the cube subtype. -/
private theorem exists_locallyHolderVersion_on_positiveCubeSubtype
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β γ T C : ℝ≥0}
    (hT : 0 < T)
    (hγ₀ : 0 < γ)
    (hγ : γ < β / α)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∃ YT : euclideanClosedCube d (T : ℝ) → Ω → E,
      (∀ t : euclideanClosedCube d (T : ℝ), X t.1 =ᵐ[μ] YT t) ∧
      (∀ ω : Ω,
        LocallyHolderWith γ (fun t : euclideanClosedCube d (T : ℝ) ↦ YT t ω)) := by
  by_cases hd : IsEmpty (Fin d)
  · letI : IsEmpty (Fin d) := hd
    let YT : euclideanClosedCube d (T : ℝ) → Ω → E := fun _ ω ↦ X 0 ω
    refine ⟨YT, ?_, ?_⟩
    · intro t
      -- Proof comment: in dimension `0`, the Euclidean cube subtype is a singleton, so the
      -- modification statement is immediate.
      have ht0 : (t : EuclideanSpace ℝ (Fin d)) = 0 := Subsingleton.elim _ _
      simpa [YT, ht0]
    · intro ω t
      -- Proof comment: in the zero-dimensional branch the chosen version is constant, hence
      -- locally Hölder with constant `0` on the whole subtype.
      refine ⟨Set.univ, Filter.univ_mem, 0, ?_⟩
      intro s _ u _
      simp [YT]
  let bad : ℕ → Set Ω := fun n ↦ cubeDyadicRowBadEvent (d := d) X T γ n
  have hαpos : 0 < (α : ℝ) := hC.p_pos
  have hγ_real : 0 < (γ : ℝ) := by
    exact_mod_cast hγ₀
  have hβ_real : 0 < (β : ℝ) := by
    have hmul_lt : (γ : ℝ) * α < β := by
      exact (lt_div_iff₀ hαpos).mp hγ
    nlinarith [hγ_real, hαpos, hmul_lt]
  have hβ : 0 < β := by
    exact_mod_cast hβ_real
  have hsumBad : Summable (fun n : ℕ ↦ μ.real (bad n)) :=
    summable_measureReal_cubeDyadicRowBadEvent
      (μ := μ)
      (X := X)
      (T := T)
      (α := α)
      (β := β)
      (C := C)
      (q := γ)
      hβ
      hC
      hγ
  have htsumBad : (∑' n : ℕ, μ (bad n)) ≠ ∞ := by
    -- Proof comment: the real-valued summability bound upgrades to the ENNReal summability
    -- hypothesis required by the first Borel-Cantelli lemma.
    simpa [ENNReal.ofReal_toReal, measure_ne_top] using hsumBad.tsum_ofReal_ne_top
  have hgood_ae : ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ bad n :=
    MeasureTheory.ae_eventually_notMem htsumBad
  -- Route correction: the ambient clipped-process detour is unnecessary here. The file already
  -- contains the cube row-good transport layer, so we package the good-row dyadic limit directly
  -- and reuse it for both fixed-time AE identification and local Hölder control.
  let YT : euclideanClosedCube d (T : ℝ) → Ω → E := cubeGoodRowVersion (d := d) X T γ hγ₀
  refine ⟨YT, ?_, ?_⟩
  · intro t
    -- Proof comment: the fixed-time modification statement comes from uniqueness of the limit in
    -- measure for the same theorem-local dyadic approximants.
    simpa [YT] using
      aeEq_original_of_cubeGoodRowVersionAt
        (d := d) (μ := μ) (X := X) (α := α) (β := β) (q := γ) (T := T) (C := C)
        hγ₀
        hC
        hgood_ae
        t
  · intro ω
    by_cases hgood : ∀ᶠ n in Filter.atTop, ω ∉ bad n
    · -- Proof comment: on good paths, the packaged limit path satisfies a small-ball Hölder
      -- estimate obtained from the same-row pair bound plus the two geometric tails.
      simpa [YT, bad] using
        locallyHolderWith_cubeGoodRowVersion_of_goodBranch
          (d := d) (X := X) (T := T) (q := γ) (ω := ω) hγ₀ hgood
    · intro x
      refine ⟨Set.univ, Filter.univ_mem, 0, ?_⟩
      -- Proof comment: on the exceptional branch the packaged version is constant by
      -- construction.
      intro s _ t _
      simp [YT, cubeGoodRowVersion, bad, hgood]

/-- Helper for Exercise 21.1.1: a single closed-cube Kolmogorov hypothesis should produce a
`γ`-Hölder version on that cube. -/
private theorem exists_holderVersion_on_nestedClosedCube
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β γ T C : ℝ≥0}
    (hγ₀ : 0 < γ)
    (hγ : γ < β / α)
    (hC : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∃ YT : euclideanClosedCube d (T : ℝ) → Ω → E,
      (∀ t : euclideanClosedCube d (T : ℝ), X t.1 =ᵐ[μ] YT t) ∧
      (∀ ω : Ω, ∃ K : ℝ≥0,
        HolderWith K γ (fun t : euclideanClosedCube d (T : ℝ) ↦ YT t ω)) := by
  classical
  by_cases hT : T = 0
  · subst hT
    let YT : euclideanClosedCube d (0 : ℝ) → Ω → E := fun _ ω ↦ X 0 ω
    refine ⟨YT, ?_, ?_⟩
    · intro t
      -- Proof comment: the zero-radius cube contains only the origin, so the modification
      -- property is tautological.
      have ht0 : (t : EuclideanSpace ℝ (Fin d)) = 0 :=
        eq_zero_of_mem_euclideanClosedCube_zero (d := d) t
      simpa [YT, ht0]
    · intro ω
      refine ⟨0, ?_⟩
      intro s t
      -- Proof comment: on the singleton cube, the version is constant, hence globally Hölder with
      -- constant `0`.
      have hs0 : (s : EuclideanSpace ℝ (Fin d)) = 0 :=
        eq_zero_of_mem_euclideanClosedCube_zero (d := d) s
      have ht0 : (t : EuclideanSpace ℝ (Fin d)) = 0 :=
        eq_zero_of_mem_euclideanClosedCube_zero (d := d) t
      simpa [YT, hs0, ht0]
  · have hTpos : 0 < T := by
      exact lt_of_le_of_ne T.2 (Ne.symm hT)
    rcases
        exists_locallyHolderVersion_on_positiveCubeSubtype
          (μ := μ)
          (X := X)
          (hT := hTpos)
          (hγ₀ := hγ₀)
          (hγ := hγ)
          (hC := hC) with
      ⟨YT, hmod, hloc⟩
    letI : CompactSpace (euclideanClosedCube d (T : ℝ)) :=
      isCompact_iff_compactSpace.mp (isCompact_euclideanClosedCube (d := d) (T := (T : ℝ)))
    refine ⟨YT, hmod, ?_⟩
    intro ω
    -- Proof comment: once the positive-radius branch gives a locally Hölder path on the compact
    -- cube subtype, compactness upgrades it to a global Hölder estimate.
    exact exists_holderWith_of_isCompactMetric (q := γ) hγ₀ (hloc ω)

-- Proof sketch: apply the Kolmogorov--Chentsov argument on each cube `[-T,T]^d`, using the
-- source-facing owner hypothesis from Remark 21.7, to obtain a `γ`-Hölder modification on that
-- cube for every `γ < β / α`. Then use consistency of the cube restrictions together with the
-- modification property to glue these local versions into one process on `ℝ^d` whose sample
-- paths are locally `γ`-Hölder everywhere.
/-- Helper for Exercise 21.1.1: the descriptive-name alias of the planned main declaration. -/
theorem exists_locallyHolderWith_version_of_euclidean_moment_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β γ : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β)
    (hγ₀ : 0 < γ) (hγ : γ < β / α)
    (hMoment :
      ∀ T : ℝ≥0, 0 < T →
        ∃ C : ℝ≥0, IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∃ Y : EuclideanSpace ℝ (Fin d) → Ω → E,
      (∀ t : EuclideanSpace ℝ (Fin d), X t =ᵐ[μ] Y t) ∧
        HasLocallyHolderPaths γ Y := by
  classical
  let cubeConst : ℕ → ℝ≥0 := fun n ↦ Classical.choose <|
    hMoment (closedCubeRadius n) (closedCubeRadius_pos n)
  have hCube :
      ∀ n : ℕ,
        IsKolmogorovProcessOnEuclideanClosedCube μ X (closedCubeRadius n) α β (cubeConst n) := by
    intro n
    exact (Classical.choose_spec <| hMoment (closedCubeRadius n) (closedCubeRadius_pos n))
  let cubeVersion :
      ∀ n : ℕ, nestedClosedCube d n → Ω → E :=
    fun n ↦ Classical.choose <|
      exists_holderVersion_on_nestedClosedCube
        (μ := μ)
        (X := X)
        (hγ₀ := hγ₀)
        (hγ := hγ)
        (hC := hCube n)
  have hCubeMod :
      ∀ n : ℕ, ∀ t : nestedClosedCube d n, X t.1 =ᵐ[μ] cubeVersion n t := by
    intro n
    exact (Classical.choose_spec <|
      exists_holderVersion_on_nestedClosedCube
        (μ := μ)
        (X := X)
        (hγ₀ := hγ₀)
        (hγ := hγ)
        (hC := hCube n)).1
  have hCubeHolder :
      ∀ n : ℕ, ∀ ω : Ω, ∃ K : ℝ≥0,
        HolderWith K γ (fun t : nestedClosedCube d n ↦ cubeVersion n t ω) := by
    intro n
    exact (Classical.choose_spec <|
      exists_holderVersion_on_nestedClosedCube
        (μ := μ)
        (X := X)
        (hγ₀ := hγ₀)
        (hγ := hγ)
        (hC := hCube n)).2
  have hGood :
      ∀ᵐ ω ∂μ, ∀ n k,
        cubeVersion n (closedCubeDensePoint (d := d) n k) ω =
          cubeVersion (n + 1)
            (closedCubeInclusion (d := d) (Nat.le_succ n)
              (closedCubeDensePoint (d := d) n k)) ω := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun k => ?_
    let t : nestedClosedCube d n := closedCubeDensePoint (d := d) n k
    filter_upwards
        [hCubeMod n t,
          hCubeMod (n + 1) (closedCubeInclusion (d := d) (Nat.le_succ n) t)] with ω hsmall hlarge
    exact hsmall.symm.trans hlarge
  let Y : EuclideanSpace ℝ (Fin d) → Ω → E := fun t ω ↦
    if hω :
        ∀ n k,
          cubeVersion n (closedCubeDensePoint (d := d) n k) ω =
            cubeVersion (n + 1)
              (closedCubeInclusion (d := d) (Nat.le_succ n)
                (closedCubeDensePoint (d := d) n k)) ω then
      cubeVersion (Nat.ceil ‖t‖) ⟨t, self_mem_nestedClosedCube (d := d) t⟩ ω
    else
      X 0 ω
  refine ⟨Y, ?_, ?_⟩
  · intro t
    filter_upwards
        [hGood, hCubeMod (Nat.ceil ‖t‖) ⟨t, self_mem_nestedClosedCube (d := d) t⟩] with ω hω hmod
    -- Proof comment: on the full-measure good branch, the patched process simply evaluates the
    -- cube version indexed by the ceiling of `‖t‖`.
    simp [Y, hω, hmod]
  · intro ω x
    by_cases hω :
        ∀ n k,
          cubeVersion n (closedCubeDensePoint (d := d) n k) ω =
            cubeVersion (n + 1)
              (closedCubeInclusion (d := d) (Nat.le_succ n)
                (closedCubeDensePoint (d := d) n k)) ω
    · let N : ℕ := Nat.ceil ‖x‖ + 1
      rcases hCubeHolder N ω with ⟨K, hK⟩
      refine ⟨Metric.ball x 1, Metric.ball_mem_nhds _ zero_lt_one, K, ?_⟩
      intro t ht u hu
      let tN : nestedClosedCube d N := ⟨t, mem_nestedClosedCube_of_mem_ball (d := d) ht⟩
      let uN : nestedClosedCube d N := ⟨u, mem_nestedClosedCube_of_mem_ball (d := d) hu⟩
      have htEq :
          Y t ω = cubeVersion N tN ω := by
        have hle : Nat.ceil ‖t‖ ≤ N := by
          have hnorm : ‖t‖ ≤ ‖x‖ + 1 := by
            have hdist : dist t x < 1 := Metric.mem_ball.1 ht
            have hlt :
                ‖t‖ < ‖x‖ + 1 := by
              calc
                ‖t‖ = ‖(t - x) + x‖ := by abel_nf
                _ ≤ ‖t - x‖ + ‖x‖ := norm_add_le _ _
                _ < 1 + ‖x‖ := by
                      gcongr
                      simpa [dist_eq_norm] using hdist
                _ = ‖x‖ + 1 := by ring
            exact le_of_lt hlt
          rw [Nat.ceil_le]
          change ‖t‖ ≤ ((Nat.ceil ‖x‖ + 1 : ℕ) : ℝ)
          have hxceil1 : ‖x‖ + 1 ≤ ((Nat.ceil ‖x‖ + 1 : ℕ) : ℝ) := by
            simpa using add_le_add_right (Nat.le_ceil ‖x‖) (1 : ℝ)
          exact le_trans hnorm hxceil1
        have hcompat :=
          nestedCubeVersion_eq_of_good
            (d := d)
            (γ := γ)
            (Y := cubeVersion)
            (hHolder := hCubeHolder)
            (hγ₀ := hγ₀)
            hω
            hle
            ⟨t, self_mem_nestedClosedCube (d := d) t⟩
        simpa [Y, hω, tN] using hcompat
      have huEq :
          Y u ω = cubeVersion N uN ω := by
        have hle : Nat.ceil ‖u‖ ≤ N := by
          have hnorm : ‖u‖ ≤ ‖x‖ + 1 := by
            have hdist : dist u x < 1 := Metric.mem_ball.1 hu
            have hlt :
                ‖u‖ < ‖x‖ + 1 := by
              calc
                ‖u‖ = ‖(u - x) + x‖ := by abel_nf
                _ ≤ ‖u - x‖ + ‖x‖ := norm_add_le _ _
                _ < 1 + ‖x‖ := by
                      gcongr
                      simpa [dist_eq_norm] using hdist
                _ = ‖x‖ + 1 := by ring
            exact le_of_lt hlt
          rw [Nat.ceil_le]
          change ‖u‖ ≤ ((Nat.ceil ‖x‖ + 1 : ℕ) : ℝ)
          have hxceil1 : ‖x‖ + 1 ≤ ((Nat.ceil ‖x‖ + 1 : ℕ) : ℝ) := by
            simpa using add_le_add_right (Nat.le_ceil ‖x‖) (1 : ℝ)
          exact le_trans hnorm hxceil1
        have hcompat :=
          nestedCubeVersion_eq_of_good
            (d := d)
            (γ := γ)
            (Y := cubeVersion)
            (hHolder := hCubeHolder)
            (hγ₀ := hγ₀)
            hω
            hle
            ⟨u, self_mem_nestedClosedCube (d := d) u⟩
        simpa [Y, hω, uN] using hcompat
      -- Proof comment: inside a unit ball around `x`, the patched process agrees with one fixed
      -- cube version, so the Hölder estimate comes directly from that version.
      calc
        edist (Y t ω) (Y u ω) = edist (cubeVersion N tN ω) (cubeVersion N uN ω) := by
          rw [htEq, huEq]
        _ ≤ K * edist tN uN ^ (γ : ℝ) := hK tN uN
        _ = K * edist t u ^ (γ : ℝ) := by
              rfl
    · refine ⟨Set.univ, Filter.univ_mem, 0, ?_⟩
      -- Proof comment: on the exceptional branch we deliberately fall back to the constant path
      -- `X 0 ω`, which is trivially Hölder on every set.
      intro t ht u hu
      simp [Y, hω]

/-- Exercise 21.1.1: if every cube restriction `[-T,T]^d` of an `ℝ^d`-indexed process satisfies
the source-facing moment bound from Remark 21.7, then the process admits a modification
whose sample paths are locally Hölder-continuous of every order `γ ∈ (0, β / α)`. -/
theorem exists_locallyHolderVersion_on_positiveClosedCube
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    {α β γ : ℝ≥0}
    (hα : 0 < α) (hβ : 0 < β)
    (hγ₀ : 0 < γ) (hγ : γ < β / α)
    (hMoment :
      ∀ T : ℝ≥0, 0 < T →
        ∃ C : ℝ≥0, IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∃ Y : EuclideanSpace ℝ (Fin d) → Ω → E,
      (∀ t : EuclideanSpace ℝ (Fin d), X t =ᵐ[μ] Y t) ∧
        HasLocallyHolderPaths γ Y := by
  -- Proof comment: expose the verified exercise statement under the planned declaration name
  -- expected by the pipeline.
  exact
    exists_locallyHolderWith_version_of_euclidean_moment_bound
      (μ := μ)
      (X := X)
      hα
      hβ
      hγ₀
      hγ
      hMoment

end ProbabilityTheory

module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Continuity
public import Mathlib.Data.Fintype.Order
public import Mathlib.Tactic.Linarith

public section

open Filter Set
open scoped Topology

namespace CompactUniformPositivity

/-- Pointwise continuity at every compact base point and strict positivity on
that slice yield one positive lower bound on a common scalar neighborhood. -/
theorem exists_uniform_lower_bound_of_pointwise_continuousAt
    {Θ : Type*} [UniformSpace Θ] [CompactSpace Θ]
    (f : ℝ → Θ → ℝ)
    (hf : ∀ θ, ContinuousAt (fun p : ℝ × Θ ↦ f p.1 p.2) (0, θ))
    (hne : Nonempty Θ) (hpos : ∀ θ, 0 < f 0 θ) :
    ∃ m > 0, ∃ δ > 0, ∀ θ ε, |ε| < δ → m ≤ f ε θ := by
  have hbase : Continuous (f 0) := by
    apply continuous_iff_continuousAt.mpr
    intro θ
    have hslice : ContinuousAt (fun θ' : Θ ↦ ((0 : ℝ), θ')) θ :=
      continuousAt_const.prodMk continuousAt_id
    have hcomp := (hf θ).comp hslice
    simpa only [Function.comp_def] using hcomp
  have huniv_nonempty : (Set.univ : Set Θ).Nonempty := by
    rcases hne with ⟨θ⟩
    exact ⟨θ, Set.mem_univ _⟩
  obtain ⟨p₀, _, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Θ)).exists_isMinOn
      huniv_nonempty hbase.continuousOn
  have ha : 0 < f 0 p₀ := hpos p₀
  let c : ℝ := f 0 p₀ / 2
  have hc : 0 < c := by
    dsimp only [c]
    exact half_pos ha
  have hP : ∀ θ ∈ (Set.univ : Set Θ), ∀ᶠ z : ℝ × Θ in 𝓝 (0, θ),
      |f z.1 z.2 - f 0 z.2| < c := by
    intro θ hθ
    have hfirst : Tendsto (fun z : ℝ × Θ ↦ f z.1 z.2)
        (𝓝 (0, θ)) (𝓝 (f 0 θ)) := hf θ
    have hsnd : ContinuousAt (Prod.snd : ℝ × Θ → Θ) (0, θ) := continuousAt_snd
    have hsecond : Tendsto (fun z : ℝ × Θ ↦ f 0 z.2)
        (𝓝 (0, θ)) (𝓝 (f 0 θ)) := by
      have hcomp := hbase.continuousAt.comp hsnd
      simpa only [Function.comp_def] using hcomp.tendsto
    have hdiff : Tendsto
        (fun z : ℝ × Θ ↦ norm (f z.1 z.2 - f 0 z.2))
        (𝓝 (0, θ)) (𝓝 0) := by
      simpa only [sub_self, norm_zero] using (hfirst.sub hsecond).norm
    have hsmall := hdiff.eventually (Iio_mem_nhds hc)
    simpa only [Real.norm_eq_abs] using hsmall
  have huniform := IsCompact.eventually_forall_of_forall_eventually
    (X := ℝ) (Y := Θ) (x₀ := (0 : ℝ))
    (P := fun ε θ ↦ |f ε θ - f 0 θ| < c)
    (isCompact_univ : IsCompact (Set.univ : Set Θ)) hP
  obtain ⟨δ, hδ, hδsubset⟩ := Metric.mem_nhds_iff.mp huniform
  refine ⟨c, hc, δ, hδ, ?_⟩
  intro θ ε hε
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  have hnear := hδsubset hεball θ (Set.mem_univ θ)
  have hnear' : |f 0 θ - f ε θ| < c := by
    simpa only [abs_sub_comm] using hnear
  have hlower : f 0 θ - c < f ε θ := by
    have hright := (abs_lt.mp hnear').2
    linarith
  have hbaseMin : f 0 p₀ ≤ f 0 θ := hmin (Set.mem_univ θ)
  dsimp only [c] at hlower ⊢
  linarith

/-- A finite family of pointwise-continuous scalar functions on a compact base
shares one positive lower bound and one common scalar neighborhood. -/
theorem exists_uniform_lower_bound_finite_of_pointwise_continuousAt
    {Θ ι : Type*} [UniformSpace Θ] [CompactSpace Θ] [Finite ι]
    (f : ℝ → Θ → ι → ℝ)
    (hf : ∀ θ i, ContinuousAt (fun p : ℝ × Θ ↦ f p.1 p.2 i) (0, θ))
    (hneΘ : Nonempty Θ) (hneι : Nonempty ι)
    (hpos : ∀ θ i, 0 < f 0 θ i) :
    ∃ m > 0, ∃ δ > 0, ∀ θ i ε, |ε| < δ → m ≤ f ε θ i := by
  classical
  let ιF : Fintype ι := Fintype.ofFinite ι
  let univι : Finset ι := @Finset.univ ι ιF
  have hι : univι.Nonempty := by
    rcases hneι with ⟨i⟩
    have hi : i ∈ univι := by
      simp [univι]
    exact ⟨i, hi⟩
  choose m hm δ hδ hbound using fun i ↦
    exists_uniform_lower_bound_of_pointwise_continuousAt
      (fun ε θ ↦ f ε θ i) (fun θ ↦ hf θ i) hneΘ (fun θ ↦ hpos θ i)
  let m₀ : ℝ := univι.inf' hι m
  let δ₀ : ℝ := univι.inf' hι δ
  have hm₀ : 0 < m₀ := by
    dsimp only [m₀]
    exact (Finset.lt_inf'_iff _).2 (fun i _ ↦ hm i)
  have hδ₀ : 0 < δ₀ := by
    dsimp only [δ₀]
    exact (Finset.lt_inf'_iff _).2 (fun i _ ↦ hδ i)
  refine ⟨m₀, hm₀, δ₀, hδ₀, ?_⟩
  intro θ i ε hε
  have hi : i ∈ univι := by
    simp [univι]
  have hδi : δ₀ ≤ δ i := Finset.inf'_le _ hi
  have hmi : m₀ ≤ m i := Finset.inf'_le _ hi
  have hεi : |ε| < δ i := lt_of_lt_of_le hε hδi
  exact hmi.trans (hbound i θ ε hεi)

end CompactUniformPositivity

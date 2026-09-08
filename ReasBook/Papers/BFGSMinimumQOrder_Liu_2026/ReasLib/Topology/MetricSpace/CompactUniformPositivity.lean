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
public import Mathlib.Data.Fintype.Order
public import Mathlib.Tactic.Linarith

public section

open Filter Set
open scoped Topology

namespace CompactUniformPositivity

/-- A jointly continuous scalar family that is strictly positive at a compact base slice
has one positive lower bound on a common parameter neighborhood. -/
theorem exists_uniform_lower_bound
    {Θ : Type*} [UniformSpace Θ] [CompactSpace Θ]
    (f : ℝ → Θ → ℝ)
    (hf : Continuous (fun p : ℝ × Θ ↦ f p.1 p.2))
    (hne : Nonempty Θ) (hpos : ∀ θ, 0 < f 0 θ) :
    ∃ m > 0, ∃ δ > 0, ∀ θ ε, |ε| < δ → m ≤ f ε θ := by
  have hg : Continuous f.uncurry := by
    change Continuous (fun p : ℝ × Θ ↦ f p.1 p.2)
    exact hf
  have hf0 : Continuous (f 0) := by
    have hslice : Continuous (fun θ : Θ ↦ ((0 : ℝ), θ)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def, Function.uncurry] using hg.comp hslice
  have huniv_nonempty : (Set.univ : Set Θ).Nonempty := by
    rcases hne with ⟨θ⟩
    exact ⟨θ, Set.mem_univ _⟩
  obtain ⟨p₀, _, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Θ)).exists_isMinOn
      huniv_nonempty hf0.continuousOn
  have ha : 0 < f 0 p₀ := hpos p₀
  have huniform : TendstoUniformly f (f 0) (𝓝 (0 : ℝ)) :=
    Continuous.tendstoUniformly f hg 0
  have hdist_event : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ θ : Θ,
      dist (f 0 θ) (f ε θ) < f 0 p₀ / 2 :=
    (Metric.tendstoUniformly_iff.mp huniform) (f 0 p₀ / 2) (half_pos ha)
  obtain ⟨δ, hδ, hδsubset⟩ := Metric.mem_nhds_iff.mp hdist_event
  refine ⟨f 0 p₀ / 2, half_pos ha, δ, hδ, ?_⟩
  intro θ ε hε
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  have hnear := hδsubset hεball θ
  have hnear' : |f 0 θ - f ε θ| < f 0 p₀ / 2 := by
    simpa only [Real.dist_eq] using hnear
  have hlower : f 0 θ - f 0 p₀ / 2 < f ε θ := by
    have hright := (abs_lt.mp hnear').2
    linarith
  have hbase : f 0 p₀ ≤ f 0 θ := hmin (Set.mem_univ θ)
  have hresult : f 0 p₀ / 2 ≤ f ε θ := by
    linarith
  exact hresult

/-- A finite collection of jointly continuous scalar families admits one lower bound and one
common parameter radius when every member is positive at the compact base slice. -/
theorem exists_uniform_lower_bound_finite
    {Θ ι : Type*} [UniformSpace Θ] [CompactSpace Θ] [Finite ι]
    (f : ℝ → Θ → ι → ℝ)
    (hf : ∀ i, Continuous (fun p : ℝ × Θ ↦ f p.1 p.2 i))
    (hneΘ : Nonempty Θ) (hneι : Nonempty ι)
    (hpos : ∀ θ i, 0 < f 0 θ i) :
    ∃ m > 0, ∃ δ > 0, ∀ θ i ε, |ε| < δ → m ≤ f ε θ i := by
  classical
  let ιF : Fintype ι := Fintype.ofFinite ι
  let univι : Finset ι := @Finset.univ ι ιF
  have hι : univι.Nonempty := by
    rcases hneι with ⟨i⟩
    exact ⟨i, by simp [univι]⟩
  choose m hm δ hδ hbound using fun i ↦
    exists_uniform_lower_bound (fun ε θ ↦ f ε θ i) (hf i) hneΘ (fun θ ↦ hpos θ i)
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
  have hεi : |ε| < δ i :=
    lt_of_lt_of_le hε (Finset.inf'_le _ (by simp [univι]))
  exact (Finset.inf'_le _ (by simp [univι])).trans (hbound i θ ε hεi)

/-- Pointwise continuity along a compact base slice and strict positivity on that slice
give one positive lower bound throughout a common scalar neighborhood. -/
theorem exists_uniform_lower_bound_of_continuousAt
    {Θ : Type*} [UniformSpace Θ] [CompactSpace Θ]
    (f : ℝ → Θ → ℝ)
    (hf : ∀ θ, ContinuousAt (fun p : ℝ × Θ ↦ f p.1 p.2) (0, θ))
    (hne : Nonempty Θ) (hpos : ∀ θ, 0 < f 0 θ) :
    ∃ m > 0, ∃ δ > 0, ∀ θ ε, |ε| < δ → m ≤ f ε θ := by
  have hf0 : Continuous (f 0) := by
    rw [continuous_iff_continuousAt]
    intro θ
    have hslice : ContinuousAt (fun θ : Θ ↦ ((0 : ℝ), θ)) θ :=
      continuousAt_const.prodMk continuousAt_id
    exact (hf θ).comp hslice
  have huniv_nonempty : (Set.univ : Set Θ).Nonempty := by
    rcases hne with ⟨θ⟩
    exact ⟨θ, Set.mem_univ _⟩
  obtain ⟨p₀, _, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Θ)).exists_isMinOn
      huniv_nonempty hf0.continuousOn
  have ha : 0 < f 0 p₀ := hpos p₀
  have hm : 0 < f 0 p₀ / 2 := half_pos ha
  have hlocal : ∀ θ : Θ, ∀ᶠ p : ℝ × Θ in 𝓝 ((0 : ℝ), θ),
      f 0 p₀ / 2 < f p.1 p.2 := by
    intro θ
    have hbase : f 0 p₀ / 2 < f 0 θ := by
      have hminθ : f 0 p₀ ≤ f 0 θ := hmin (Set.mem_univ θ)
      linarith
    exact (hf θ).eventually (Ioi_mem_nhds hbase)
  have hevent : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ θ : Θ, f 0 p₀ / 2 < f ε θ := by
    have hall := IsCompact.eventually_forall_of_forall_eventually
      (X := ℝ) (x₀ := (0 : ℝ))
      (P := fun ε θ ↦ f 0 p₀ / 2 < f ε θ)
      (isCompact_univ : IsCompact (Set.univ : Set Θ))
      (fun θ _ ↦ hlocal θ)
    simpa only [Set.mem_univ, forall_const] using hall
  obtain ⟨δ, hδ, hδsubset⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨f 0 p₀ / 2, hm, δ, hδ, ?_⟩
  intro θ ε hε
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hε
  exact (hδsubset hεball θ).le

/-- A finite family that is pointwise continuous along a compact base slice and
strictly positive there has one lower bound on one common scalar neighborhood. -/
theorem exists_uniform_lower_bound_finite_of_continuousAt
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
    exists_uniform_lower_bound_of_continuousAt (fun ε θ ↦ f ε θ i)
      (fun θ ↦ hf θ i) hneΘ (fun θ ↦ hpos θ i)
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
  have hm_le : m₀ ≤ m i := Finset.inf'_le _ hi
  have hδ_le : δ₀ ≤ δ i := Finset.inf'_le _ hi
  have hεi : |ε| < δ i := lt_of_lt_of_le hε hδ_le
  exact hm_le.trans (hbound i θ ε hεi)

end CompactUniformPositivity

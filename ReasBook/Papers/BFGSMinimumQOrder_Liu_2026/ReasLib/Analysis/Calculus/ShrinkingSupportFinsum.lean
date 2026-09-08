module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Set.Pairwise.Basic
public import ReasLib.Topology.MetricSpace.ShrinkingBalls

public section

open Filter Topology

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A pointwise locally finite family of topological supports agrees near a point with the
finite sum indexed by the supports containing that point. -/
private lemma finsumLocalNormalForm {X M ι : Type*} [TopologicalSpace X] [AddCommMonoid M]
    (f : ι → X → M) (x : X)
    (hlocal : ∃ s ∈ 𝓝 x, {i | (tsupport (f i) ∩ s).Nonempty}.Finite) :
    ∃ I : Finset ι, (∀ i, i ∈ I ↔ x ∈ tsupport (f i)) ∧
      (fun y ↦ ∑ᶠ i, f i y) =ᶠ[𝓝 x] fun y ↦ ∑ i ∈ I, f i y := by
  classical
  obtain ⟨s, hs, hfinite⟩ := hlocal
  let K : Finset ι := hfinite.toFinset
  let I : Finset ι := K.filter fun i ↦ x ∈ tsupport (f i)
  have hxs : x ∈ s := mem_of_mem_nhds hs
  have hxK (i : ι) (hi : x ∈ tsupport (f i)) : i ∈ K := by
    simp only [K, Set.Finite.mem_toFinset]
    exact ⟨x, hi, hxs⟩
  have hI (i : ι) : i ∈ I ↔ x ∈ tsupport (f i) := by
    simp only [I, Finset.mem_filter]
    constructor
    · exact fun hi ↦ hi.2
    · exact fun hi ↦ ⟨hxK i hi, hi⟩
  let J : Finset ι := K.filter fun i ↦ x ∉ tsupport (f i)
  -- Remove the finitely many supports in the meeting set which do not contain the base point.
  have havoid : ⋂ i ∈ J, (tsupport (f i))ᶜ ∈ 𝓝 x := by
    refine (Filter.biInter_finset_mem J).mpr ?_
    intro i hi
    exact (isClosed_tsupport (f i)).compl_mem_nhds (Finset.mem_filter.mp hi).2
  refine ⟨I, hI, ?_⟩
  -- On the resulting neighborhood every nonzero summand has an index in `I`.
  filter_upwards [inter_mem hs havoid] with y hy
  apply finsum_eq_sum_of_support_subset
  intro i hi
  have hytsupport : y ∈ tsupport (f i) := subset_tsupport (f i) hi
  have hiK : i ∈ K := by
    simp only [K, Set.Finite.mem_toFinset]
    exact ⟨y, hytsupport, hy.1⟩
  apply Finset.mem_filter.mpr
  refine ⟨hiK, ?_⟩
  by_contra hix
  have hiJ : i ∈ J := by
    exact Finset.mem_filter.mpr ⟨hiK, hix⟩
  have hycompl : y ∈ (tsupport (f i))ᶜ :=
    Set.mem_iInter.mp (Set.mem_iInter.mp hy.2 i) hiJ
  exact hycompl hytsupport

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Topological supports contained in shrinking, pairwise-disjoint closed balls are locally
finite away from a closed set containing every `atTop` cluster point of their centers. -/
theorem locallyFinite_tsupport_outside (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ)
    (ψ : ℕ → E → F)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) :
    ∀ z ∈ Γᶜ, ∃ s ∈ 𝓝 z, {k | (tsupport (ψ k) ∩ s).Nonempty}.Finite := by
  intro z hz
  -- First obtain a neighborhood meeting only finitely many of the containing closed balls.
  obtain ⟨s, hs, hfinite⟩ :=
    Metric.locallyFinite_closedBall_outside Γ x ρ hρ0 hcluster z hz
  refine ⟨s, hs, hfinite.subset ?_⟩
  -- Support containment transfers every nonempty support intersection to a ball intersection.
  intro k hk
  obtain ⟨w, hwtsupport, hws⟩ := hk
  exact ⟨w, hsupport k hwtsupport, hws⟩

/-- The pointwise finsum of smooth functions supported in shrinking, pairwise-disjoint closed
balls is smooth away from a closed set containing the cluster points of the centers. -/
theorem contDiffOn_finsum_outside (m : ℕ) (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ)
    (ψ : ℕ → E → F) (hΓ : IsClosed Γ)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k))
    (hsmooth : ∀ k, ContDiff ℝ m (ψ k)) :
    ContDiffOn ℝ m (fun z ↦ ∑ᶠ k, ψ k z) Γᶜ := by
  rw [hΓ.isOpen_compl.contDiffOn_iff]
  intro z hz
  -- Normalize the finsum near `z` to the finite family of supports containing `z`.
  obtain ⟨I, hI, hlocal⟩ := finsumLocalNormalForm ψ z
    (locallyFinite_tsupport_outside Γ x ρ ψ hcluster hρ0 hsupport z hz)
  have hsum : ContDiff ℝ m (fun y ↦ ∑ i ∈ I, ψ i y) := by
    exact ContDiff.sum fun i _ ↦ hsmooth i
  -- Smoothness of the finite normal form transfers across the local equality.
  exact hsum.contDiffAt.congr_of_eventuallyEq hlocal

/-- Away from the cluster set, the iterated derivatives of a pointwise finsum agree with those
of the summand whose topological support contains the point. -/
theorem iteratedFDeriv_finsum_eq_of_mem_tsupport (Γ : Set E) (x : ℕ → E)
    (ρ : ℕ → ℝ) (ψ : ℕ → E → F)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.closedBall (x k) (ρ k)))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) {z : E} (hz : z ∈ Γᶜ) {k j : ℕ}
    (hzk : z ∈ tsupport (ψ k)) :
    iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) z = iteratedFDeriv ℝ j (ψ k) z := by
  obtain ⟨I, hI, hlocal⟩ := finsumLocalNormalForm ψ z
    (locallyFinite_tsupport_outside Γ x ρ ψ hcluster hρ0 hsupport z hz)
  -- Pairwise disjointness makes the active index set the singleton `{k}`.
  have hdisjoint : Set.univ.PairwiseDisjoint (fun n ↦ tsupport (ψ n)) :=
    hballs.mono hsupport
  have hIeq : I = {k} := by
    ext n
    rw [hI n, Finset.mem_singleton]
    constructor
    · intro hn
      exact hdisjoint.elim_set (Set.mem_univ n) (Set.mem_univ k) z hn hzk
    · intro hnk
      rw [hnk]
      exact hzk
  have hsummand : (fun w ↦ ∑ᶠ n, ψ n w) =ᶠ[𝓝 z] ψ k := by
    simpa only [hIeq, Finset.sum_singleton] using hlocal
  -- Eventual equality transports every iterated derivative, in particular order `j`.
  exact (hsummand.iteratedFDeriv ℝ j).eq_of_nhds

/-- Away from the cluster set, every iterated derivative through the smoothness order of a
pointwise finsum vanishes at a point outside all topological supports. -/
theorem iteratedFDeriv_finsum_eq_zero (Γ : Set E) (x : ℕ → E) (ρ : ℕ → ℝ)
    (ψ : ℕ → E → F)
    (hcluster : ∀ y, MapClusterPt y atTop x → y ∈ Γ)
    (hρ0 : Tendsto ρ atTop (𝓝 0))
    (hsupport : ∀ k, tsupport (ψ k) ⊆ Metric.closedBall (x k) (ρ k)) {z : E} (hz : z ∈ Γᶜ)
    (hzsupport : ∀ k, z ∉ tsupport (ψ k)) {j : ℕ} :
    iteratedFDeriv ℝ j (fun w ↦ ∑ᶠ n, ψ n w) z = 0 := by
  obtain ⟨I, hI, hlocal⟩ := finsumLocalNormalForm ψ z
    (locallyFinite_tsupport_outside Γ x ρ ψ hcluster hρ0 hsupport z hz)
  -- With no active support, the finite local normal form has no indices.
  have hIeq : I = ∅ := by
    exact Finset.eq_empty_of_forall_notMem fun k hk ↦ hzsupport k ((hI k).mp hk)
  have hzero : (fun w ↦ ∑ᶠ n, ψ n w) =ᶠ[𝓝 z] fun _ ↦ (0 : F) := by
    simpa only [hIeq, Finset.sum_empty] using hlocal
  -- Transport the derivative to the zero function and use its canonical derivative formula.
  simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply] using
    (hzero.iteratedFDeriv ℝ j).eq_of_nhds

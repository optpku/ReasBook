/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

variable {X : Type u}

/-- The set of sequential limit inferiors of `f` at `x`. -/
def sequentialLiminfValuesAt [TopologicalSpace X] (f : X → EReal) (x : X) :
    Set EReal :=
  {r | ∃ u : ℕ → X, Tendsto u atTop (nhds x) ∧ liminf (f ∘ u) atTop = r}

private theorem clusterPt_liminf_map_nhds [TopologicalSpace X] (f : X → EReal) (x : X) :
    ClusterPt (liminf f (nhds x)) (map f (nhds x)) := by
  let L := liminf f (nhds x)
  rcases eq_or_ne L ⊤ with htop | htop
  · rw [clusterPt_iff_frequently]
    intro s hs
    have hs_top : s ∈ nhds (⊤ : EReal) := by
      simpa [L, htop] using hs
    rcases EReal.nhds_top_basis.mem_iff.1 hs_top with ⟨a, -, ha⟩
    have hgt : ∀ᶠ y in nhds x, (a : EReal) < f y := by
      have : (a : EReal) < liminf f (nhds x) := by
        simp [L, htop]
      exact eventually_lt_of_lt_liminf this
    have hmem : ∀ᶠ z in map f (nhds x), z ∈ Set.Ioi (a : EReal) := by
      simpa [Filter.Eventually, mem_map'] using hgt
    exact hmem.frequently.mono fun z hz ↦ ha hz
  · rcases eq_or_ne L ⊥ with hbot | hbot
    · rw [clusterPt_iff_frequently]
      intro s hs
      have hs_bot : s ∈ nhds (⊥ : EReal) := by
        simpa [L, hbot] using hs
      rcases EReal.nhds_bot_basis.mem_iff.1 hs_bot with ⟨a, -, ha⟩
      have hlt : ∃ᶠ y in nhds x, f y < (a : EReal) := by
        have : liminf f (nhds x) < (a : EReal) := by
          simp [L, hbot]
        exact frequently_lt_of_liminf_lt (by isBoundedDefault) this
      have hmem : ∃ᶠ z in map f (nhds x), z ∈ Set.Iio (a : EReal) := by
        simpa [Filter.Frequently, Filter.Eventually, mem_map'] using hlt
      exact hmem.mono fun z hz ↦ ha hz
    · have hLfin : ((L.toReal : EReal) = L) := EReal.coe_toReal htop hbot
      have hbasis : (nhds L).HasBasis
          (fun p : ℝ × ℝ ↦ p.1 < L.toReal ∧ L.toReal < p.2)
          (fun p ↦ Set.Ioo (p.1 : EReal) (p.2 : EReal)) := by
        rw [← hLfin, EReal.nhds_coe]
        simpa [EReal.image_coe_Ioo] using
          (Filter.HasBasis.map (fun r : ℝ ↦ (r : EReal)) (nhds_basis_Ioo L.toReal))
      rw [clusterPt_iff_frequently]
      intro s hs
      rcases hbasis.mem_iff.mp hs with ⟨p, hp, hps⟩
      have hgt : ∀ᶠ y in nhds x, (p.1 : EReal) < f y := by
        have hp1 : (p.1 : EReal) < L := by
          calc
            (p.1 : EReal) < (L.toReal : EReal) := by
              exact_mod_cast hp.1
            _ = L := hLfin
        have : (p.1 : EReal) < liminf f (nhds x) := by
          simpa [L] using hp1
        exact eventually_lt_of_lt_liminf this
      have hlt : ∃ᶠ y in nhds x, f y < (p.2 : EReal) := by
        have hp2 : L < (p.2 : EReal) := by
          calc
            L = (L.toReal : EReal) := hLfin.symm
            _ < (p.2 : EReal) := by
              exact_mod_cast hp.2
        have : liminf f (nhds x) < (p.2 : EReal) := by
          simpa [L] using hp2
        exact frequently_lt_of_liminf_lt (by isBoundedDefault) this
      exact (hlt.and_eventually hgt).mono fun y hy ↦ hps ⟨hy.2, hy.1⟩

private theorem liminf_mem_sequentialLiminfValuesAt [MetricSpace X] (f : X → EReal) (x : X) :
    liminf f (nhds x) ∈ sequentialLiminfValuesAt f x := by
  let L := liminf f (nhds x)
  have hcluster : ClusterPt L (map f (nhds x)) := by
    simpa [L] using clusterPt_liminf_map_nhds f x
  have hne : NeBot (nhds x ⊓ comap f (nhds L)) := by
    have hmap : NeBot (map f (comap f (nhds L) ⊓ nhds x)) := by
      rw [show map f (comap f (nhds L) ⊓ nhds x) = nhds L ⊓ map f (nhds x) by
        simpa [inf_comm] using (Filter.push_pull' f (nhds x) (nhds L))]
      simpa [ClusterPt] using hcluster
    have hsource : NeBot (comap f (nhds L) ⊓ nhds x) := NeBot.of_map hmap
    simpa [inf_comm] using hsource
  haveI : NeBot (nhds x ⊓ comap f (nhds L)) := hne
  rcases exists_seq_tendsto (nhds x ⊓ comap f (nhds L)) with ⟨u, hu⟩
  have hu' := tendsto_inf.1 hu
  refine ⟨u, hu'.1, ?_⟩
  have hfu : Tendsto (f ∘ u) atTop (nhds L) := by
    simpa [tendsto_iff_comap, Function.comp, comap_comap] using hu'.2
  simpa [L] using hfu.liminf_eq

private theorem liminfAt_le_of_mem_sequentialLiminfValuesAt [TopologicalSpace X] (f : X → EReal)
    (x : X) {r : EReal} (hr : r ∈ sequentialLiminfValuesAt f x) :
    liminf f (nhds x) ≤ r := by
  rcases hr with ⟨u, hu, rfl⟩
  simpa using (liminf_le_liminf_of_le hu : liminf f (nhds x) ≤ liminf f (map u atTop))

-- Proof sketch: the lower bound follows from the monotonicity of `Filter.liminf` under any
-- convergent sequence `u : ℕ → X`. For the reverse inequality, use the metric neighborhood basis
-- of shrinking balls around `x`, choose points whose function values approximate the infimum on
-- each ball, and show that the resulting sequence converges to `x` and realizes the neighborhood
-- `liminf`.
/-- Lemma 1.42: in a metric space, the neighborhood-filter limit inferior of `f` at `x` is the
minimum of the sequential limit inferiors along sequences converging to `x`. -/
theorem liminfAt_isLeast_sequentialLiminfValues [MetricSpace X] (f : X → EReal)
    (x : X) : IsLeast (sequentialLiminfValuesAt f x) (liminf f (nhds x)) := by
  exact ⟨liminf_mem_sequentialLiminfValuesAt f x, fun r hr ↦
    liminfAt_le_of_mem_sequentialLiminfValuesAt f x hr⟩
